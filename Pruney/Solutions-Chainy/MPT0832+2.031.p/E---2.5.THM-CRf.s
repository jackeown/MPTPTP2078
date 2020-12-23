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
% DateTime   : Thu Dec  3 10:57:54 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 102 expanded)
%              Number of clauses        :   24 (  43 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 187 expanded)
%              Number of equality atoms :    8 (  20 expanded)
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

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(dt_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k6_relset_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relset_1)).

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
    ! [X23,X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k6_relset_1(X23,X24,X25,X26) = k8_relat_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_14,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | m1_subset_1(k6_relset_1(X16,X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_relset_1])])).

cnf(c_0_16,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k6_relset_1(X2,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k6_relset_1(esk3_0,esk1_0,X1,esk4_0) = k8_relat_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(k2_relat_1(k8_relat_1(X11,X12)),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(k1_relset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_26,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

fof(c_0_28,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(k1_relat_1(X29),X27)
      | ~ r1_tarski(k2_relat_1(X29),X28)
      | m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

fof(c_0_31,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | m1_subset_1(X5,k1_zfmisc_1(X6)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk3_0,esk1_0,k8_relat_1(X1,esk4_0)) = k1_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_19])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_relat_1(k8_relat_1(X1,esk4_0)),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27])])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.18/0.39  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.027 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t35_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 0.18/0.39  fof(redefinition_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k6_relset_1(X1,X2,X3,X4)=k8_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 0.18/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.39  fof(dt_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k6_relset_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relset_1)).
% 0.18/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.39  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.18/0.39  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.18/0.39  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.18/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), inference(assume_negation,[status(cth)],[t35_relset_1])).
% 0.18/0.39  fof(c_0_11, plain, ![X23, X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k6_relset_1(X23,X24,X25,X26)=k8_relat_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).
% 0.18/0.39  fof(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))&~m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.18/0.39  fof(c_0_13, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.39  fof(c_0_14, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.39  fof(c_0_15, plain, ![X16, X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|m1_subset_1(k6_relset_1(X16,X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_relset_1])])).
% 0.18/0.39  cnf(c_0_16, plain, (k6_relset_1(X2,X3,X4,X1)=k8_relat_1(X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  cnf(c_0_19, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  fof(c_0_20, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k1_relset_1(X20,X21,X22)=k1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.39  cnf(c_0_21, plain, (m1_subset_1(k6_relset_1(X2,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_22, negated_conjecture, (k6_relset_1(esk3_0,esk1_0,X1,esk4_0)=k8_relat_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.39  fof(c_0_23, plain, ![X11, X12]:(~v1_relat_1(X12)|r1_tarski(k2_relat_1(k8_relat_1(X11,X12)),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.18/0.39  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.39  fof(c_0_25, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|m1_subset_1(k1_relset_1(X13,X14,X15),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.18/0.39  cnf(c_0_26, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.18/0.39  fof(c_0_28, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(k1_relat_1(X29),X27)|~r1_tarski(k2_relat_1(X29),X28)|m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.18/0.39  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.18/0.39  fof(c_0_31, plain, ![X5, X6]:((~m1_subset_1(X5,k1_zfmisc_1(X6))|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|m1_subset_1(X5,k1_zfmisc_1(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.39  cnf(c_0_32, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk3_0,esk1_0,k8_relat_1(X1,esk4_0))=k1_relat_1(k8_relat_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.39  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.39  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.39  cnf(c_0_36, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_19])])).
% 0.18/0.39  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_38, negated_conjecture, (m1_subset_1(k1_relat_1(k8_relat_1(X1,esk4_0)),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27])])).
% 0.18/0.39  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.18/0.39  cnf(c_0_41, negated_conjecture, (r1_tarski(k1_relat_1(k8_relat_1(X1,esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.39  cnf(c_0_42, negated_conjecture, (~m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(rw,[status(thm)],[c_0_39, c_0_22])).
% 0.18/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 45
% 0.18/0.39  # Proof object clause steps            : 24
% 0.18/0.39  # Proof object formula steps           : 21
% 0.18/0.39  # Proof object conjectures             : 17
% 0.18/0.39  # Proof object clause conjectures      : 14
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 11
% 0.18/0.39  # Proof object initial formulas used   : 10
% 0.18/0.39  # Proof object generating inferences   : 11
% 0.18/0.39  # Proof object simplifying inferences  : 11
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 10
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 12
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 12
% 0.18/0.39  # Processed clauses                    : 238
% 0.18/0.39  # ...of these trivial                  : 6
% 0.18/0.39  # ...subsumed                          : 52
% 0.18/0.39  # ...remaining for further processing  : 180
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 0
% 0.18/0.39  # Backward-rewritten                   : 9
% 0.18/0.39  # Generated clauses                    : 891
% 0.18/0.39  # ...of the previous two non-trivial   : 767
% 0.18/0.39  # Contextual simplify-reflections      : 0
% 0.18/0.39  # Paramodulations                      : 891
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 0
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 159
% 0.18/0.39  #    Positive orientable unit clauses  : 34
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 0
% 0.18/0.39  #    Non-unit-clauses                  : 125
% 0.18/0.39  # Current number of unprocessed clauses: 549
% 0.18/0.39  # ...number of literals in the above   : 1609
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 21
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 4336
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 2943
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 52
% 0.18/0.39  # Unit Clause-clause subsumption calls : 21
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 70
% 0.18/0.39  # BW rewrite match successes           : 5
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 16273
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.045 s
% 0.18/0.39  # System time              : 0.008 s
% 0.18/0.39  # Total time               : 0.053 s
% 0.18/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
