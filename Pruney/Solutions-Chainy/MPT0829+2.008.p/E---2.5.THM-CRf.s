%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:32 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   46 (  93 expanded)
%              Number of clauses        :   25 (  36 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 243 expanded)
%              Number of equality atoms :   24 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k1_relset_1(X1,X2,X3))
          & X2 = k2_relset_1(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t30_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(k6_relat_1(X3),X4)
       => ( r1_tarski(X3,k1_relset_1(X1,X2,X4))
          & r1_tarski(X3,k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k1_relset_1(X1,X2,X3))
            & X2 = k2_relset_1(X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_relset_1])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( ( v4_relat_1(X18,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v5_relat_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(k6_relat_1(esk2_0),esk3_0)
    & ( ~ r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))
      | esk2_0 != k2_relset_1(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r1_tarski(k2_relat_1(X12),X11)
      | k5_relat_1(X12,k6_relat_1(X11)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ r1_tarski(k1_relat_1(X10),X9)
      | k5_relat_1(k6_relat_1(X9),X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_16,plain,(
    ! [X8] :
      ( k1_relat_1(k6_relat_1(X8)) = X8
      & k2_relat_1(k6_relat_1(X8)) = X8 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_17,plain,(
    ! [X7] : v1_relat_1(k6_relat_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_18,plain,(
    ! [X5,X6] :
      ( ( ~ v5_relat_1(X6,X5)
        | r1_tarski(k2_relat_1(X6),X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r1_tarski(k2_relat_1(X6),X5)
        | v5_relat_1(X6,X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_19,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r1_tarski(X24,k1_relset_1(X22,X23,X25))
        | ~ r1_tarski(k6_relat_1(X24),X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( r1_tarski(X24,k2_relset_1(X22,X23,X25))
        | ~ r1_tarski(k6_relat_1(X24),X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relset_1])])])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_relset_1(X19,X20,X21) = k2_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_24,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))
    | esk2_0 != k2_relset_1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k1_relset_1(X2,X3,X4))
    | ~ r1_tarski(k6_relat_1(X1),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k6_relat_1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k6_relat_1(X1) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_27])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20]),c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k6_relat_1(k2_relat_1(esk3_0)) = k6_relat_1(esk2_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk3_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_relset_1(X2,X3,X4))
    | ~ r1_tarski(k6_relat_1(X1),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_40]),c_0_26]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk3_0))
    | ~ r1_tarski(k6_relat_1(X1),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_20]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:55:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.028 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t32_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r1_tarski(k6_relat_1(X2),X3)=>(r1_tarski(X2,k1_relset_1(X1,X2,X3))&X2=k2_relset_1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 0.12/0.36  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.36  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.36  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.12/0.36  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.12/0.36  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.36  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.12/0.36  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.12/0.36  fof(t30_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r1_tarski(k6_relat_1(X3),X4)=>(r1_tarski(X3,k1_relset_1(X1,X2,X4))&r1_tarski(X3,k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 0.12/0.36  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.36  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r1_tarski(k6_relat_1(X2),X3)=>(r1_tarski(X2,k1_relset_1(X1,X2,X3))&X2=k2_relset_1(X1,X2,X3))))), inference(assume_negation,[status(cth)],[t32_relset_1])).
% 0.12/0.36  fof(c_0_11, plain, ![X16, X17, X18]:((v4_relat_1(X18,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(v5_relat_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.36  fof(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))&(r1_tarski(k6_relat_1(esk2_0),esk3_0)&(~r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))|esk2_0!=k2_relset_1(esk1_0,esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.36  fof(c_0_13, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.36  fof(c_0_14, plain, ![X11, X12]:(~v1_relat_1(X12)|(~r1_tarski(k2_relat_1(X12),X11)|k5_relat_1(X12,k6_relat_1(X11))=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.12/0.36  fof(c_0_15, plain, ![X9, X10]:(~v1_relat_1(X10)|(~r1_tarski(k1_relat_1(X10),X9)|k5_relat_1(k6_relat_1(X9),X10)=X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.12/0.36  fof(c_0_16, plain, ![X8]:(k1_relat_1(k6_relat_1(X8))=X8&k2_relat_1(k6_relat_1(X8))=X8), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.36  fof(c_0_17, plain, ![X7]:v1_relat_1(k6_relat_1(X7)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.12/0.36  fof(c_0_18, plain, ![X5, X6]:((~v5_relat_1(X6,X5)|r1_tarski(k2_relat_1(X6),X5)|~v1_relat_1(X6))&(~r1_tarski(k2_relat_1(X6),X5)|v5_relat_1(X6,X5)|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.12/0.36  cnf(c_0_19, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  fof(c_0_22, plain, ![X22, X23, X24, X25]:((r1_tarski(X24,k1_relset_1(X22,X23,X25))|~r1_tarski(k6_relat_1(X24),X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(r1_tarski(X24,k2_relset_1(X22,X23,X25))|~r1_tarski(k6_relat_1(X24),X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relset_1])])])).
% 0.12/0.36  fof(c_0_23, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k2_relset_1(X19,X20,X21)=k2_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.36  cnf(c_0_24, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_25, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_26, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_27, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_28, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (~r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))|esk2_0!=k2_relset_1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_33, plain, (r1_tarski(X1,k1_relset_1(X2,X3,X4))|~r1_tarski(k6_relat_1(X1),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (r1_tarski(k6_relat_1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_35, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_36, plain, (k6_relat_1(X1)=k6_relat_1(X2)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_27])])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_20]), c_0_34])])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (k6_relat_1(k2_relat_1(esk3_0))=k6_relat_1(esk2_0)|~r1_tarski(esk2_0,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk3_0)!=esk2_0), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.36  cnf(c_0_42, plain, (r1_tarski(X1,k2_relset_1(X2,X3,X4))|~r1_tarski(k6_relat_1(X1),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_43, negated_conjecture, (~r1_tarski(esk2_0,k2_relat_1(esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_40]), c_0_26]), c_0_41])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk3_0))|~r1_tarski(k6_relat_1(X1),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_20]), c_0_39])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 46
% 0.12/0.36  # Proof object clause steps            : 25
% 0.12/0.36  # Proof object formula steps           : 21
% 0.12/0.36  # Proof object conjectures             : 16
% 0.12/0.36  # Proof object clause conjectures      : 13
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 14
% 0.12/0.36  # Proof object initial formulas used   : 10
% 0.12/0.36  # Proof object generating inferences   : 10
% 0.12/0.36  # Proof object simplifying inferences  : 16
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 10
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 16
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 16
% 0.12/0.36  # Processed clauses                    : 47
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 2
% 0.12/0.36  # ...remaining for further processing  : 45
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 2
% 0.12/0.36  # Generated clauses                    : 24
% 0.12/0.36  # ...of the previous two non-trivial   : 22
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 24
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 27
% 0.12/0.36  #    Positive orientable unit clauses  : 10
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 2
% 0.12/0.36  #    Non-unit-clauses                  : 15
% 0.12/0.36  # Current number of unprocessed clauses: 7
% 0.12/0.36  # ...number of literals in the above   : 24
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 18
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 27
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 25
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.36  # Unit Clause-clause subsumption calls : 18
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1482
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.030 s
% 0.12/0.36  # System time              : 0.003 s
% 0.12/0.36  # Total time               : 0.033 s
% 0.12/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
