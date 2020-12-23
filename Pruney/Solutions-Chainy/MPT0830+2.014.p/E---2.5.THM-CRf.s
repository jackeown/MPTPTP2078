%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:37 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 245 expanded)
%              Number of clauses        :   34 ( 111 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 511 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

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

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t33_relset_1])).

fof(c_0_11,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k5_relset_1(X23,X24,X25,X26) = k7_relat_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_14,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ r1_tarski(X31,X34)
      | m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(k7_relat_1(X16,X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k5_relset_1(esk1_0,esk3_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_21,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X29)))
      | ~ r1_tarski(k1_relat_1(X30),X28)
      | m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k7_relat_1(esk4_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))
    | ~ r1_tarski(k1_relat_1(X4),X2)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X5,X6] :
      ( ( ~ v4_relat_1(X6,X5)
        | r1_tarski(k1_relat_1(X6),X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r1_tarski(k1_relat_1(X6),X5)
        | v4_relat_1(X6,X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_33,plain,(
    ! [X7,X8,X9] :
      ( ( v1_relat_1(k7_relat_1(X9,X7))
        | ~ v1_relat_1(X9)
        | ~ v4_relat_1(X9,X8) )
      & ( v4_relat_1(k7_relat_1(X9,X7),X7)
        | ~ v1_relat_1(X9)
        | ~ v4_relat_1(X9,X8) )
      & ( v4_relat_1(k7_relat_1(X9,X7),X8)
        | ~ v1_relat_1(X9)
        | ~ v4_relat_1(X9,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

fof(c_0_34,plain,(
    ! [X20,X21,X22] :
      ( ( v4_relat_1(X22,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v5_relat_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ r1_tarski(k7_relat_1(esk4_0,esk2_0),X3)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)
    | ~ r1_tarski(k7_relat_1(esk4_0,esk2_0),X2)
    | ~ r1_tarski(X2,k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k7_relat_1(k7_relat_1(esk4_0,X1),X2),k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v4_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_15])).

fof(c_0_45,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ v4_relat_1(X14,X13)
      | X14 = k7_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk4_0,esk2_0),k7_relat_1(k7_relat_1(esk4_0,X1),X2))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_24])])).

cnf(c_0_48,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk4_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk4_0,esk2_0),k7_relat_1(k7_relat_1(esk4_0,esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk4_0,X1),esk1_0) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_36])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk4_0,esk2_0),k7_relat_1(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n024.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:14:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 1.45/1.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 1.45/1.65  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 1.45/1.65  #
% 1.45/1.65  # Preprocessing time       : 0.028 s
% 1.45/1.65  # Presaturation interreduction done
% 1.45/1.65  
% 1.45/1.65  # Proof found!
% 1.45/1.65  # SZS status Theorem
% 1.45/1.65  # SZS output start CNFRefutation
% 1.45/1.65  fof(t33_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 1.45/1.65  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.45/1.65  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.45/1.65  fof(t4_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>(r1_tarski(X1,X4)=>m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 1.45/1.65  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.45/1.65  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 1.45/1.65  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.45/1.65  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 1.45/1.65  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.45/1.65  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.45/1.65  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(assume_negation,[status(cth)],[t33_relset_1])).
% 1.45/1.65  fof(c_0_11, plain, ![X23, X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k5_relset_1(X23,X24,X25,X26)=k7_relat_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 1.45/1.65  fof(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))&~m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 1.45/1.65  fof(c_0_13, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.45/1.65  cnf(c_0_14, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.45/1.65  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.45/1.65  fof(c_0_16, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|(~r1_tarski(X31,X34)|m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).
% 1.45/1.65  fof(c_0_17, plain, ![X15, X16]:(~v1_relat_1(X16)|r1_tarski(k7_relat_1(X16,X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 1.45/1.65  cnf(c_0_18, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.45/1.65  cnf(c_0_19, negated_conjecture, (~m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.45/1.65  cnf(c_0_20, negated_conjecture, (k5_relset_1(esk1_0,esk3_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.45/1.65  fof(c_0_21, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X29)))|(~r1_tarski(k1_relat_1(X30),X28)|m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 1.45/1.65  cnf(c_0_22, plain, (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.45/1.65  cnf(c_0_23, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.45/1.65  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 1.45/1.65  cnf(c_0_25, negated_conjecture, (~m1_subset_1(k7_relat_1(esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 1.45/1.65  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.45/1.65  cnf(c_0_27, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_15])).
% 1.45/1.65  cnf(c_0_28, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.45/1.65  cnf(c_0_29, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~r1_tarski(k7_relat_1(esk4_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 1.45/1.65  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))|~r1_tarski(k1_relat_1(X4),X2)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 1.45/1.65  cnf(c_0_31, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.45/1.65  fof(c_0_32, plain, ![X5, X6]:((~v4_relat_1(X6,X5)|r1_tarski(k1_relat_1(X6),X5)|~v1_relat_1(X6))&(~r1_tarski(k1_relat_1(X6),X5)|v4_relat_1(X6,X5)|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.45/1.65  fof(c_0_33, plain, ![X7, X8, X9]:(((v1_relat_1(k7_relat_1(X9,X7))|(~v1_relat_1(X9)|~v4_relat_1(X9,X8)))&(v4_relat_1(k7_relat_1(X9,X7),X7)|(~v1_relat_1(X9)|~v4_relat_1(X9,X8))))&(v4_relat_1(k7_relat_1(X9,X7),X8)|(~v1_relat_1(X9)|~v4_relat_1(X9,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 1.45/1.65  fof(c_0_34, plain, ![X20, X21, X22]:((v4_relat_1(X22,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v5_relat_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.45/1.65  cnf(c_0_35, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~r1_tarski(k7_relat_1(esk4_0,esk2_0),X3)|~r1_tarski(k1_relat_1(X1),esk2_0)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.45/1.65  cnf(c_0_36, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 1.45/1.65  cnf(c_0_37, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.45/1.65  cnf(c_0_38, plain, (v4_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.45/1.65  cnf(c_0_39, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.45/1.65  cnf(c_0_40, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.45/1.65  cnf(c_0_41, negated_conjecture, (~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)|~r1_tarski(k7_relat_1(esk4_0,esk2_0),X2)|~r1_tarski(X2,k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 1.45/1.65  cnf(c_0_42, negated_conjecture, (r1_tarski(k7_relat_1(k7_relat_1(esk4_0,X1),X2),k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_23, c_0_36])).
% 1.45/1.65  cnf(c_0_43, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 1.45/1.65  cnf(c_0_44, negated_conjecture, (v4_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_40, c_0_15])).
% 1.45/1.65  fof(c_0_45, plain, ![X13, X14]:(~v1_relat_1(X14)|~v4_relat_1(X14,X13)|X14=k7_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 1.45/1.65  cnf(c_0_46, negated_conjecture, (~r1_tarski(k7_relat_1(esk4_0,esk2_0),k7_relat_1(k7_relat_1(esk4_0,X1),X2))|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.45/1.65  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_24])])).
% 1.45/1.65  cnf(c_0_48, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.45/1.65  cnf(c_0_49, negated_conjecture, (v4_relat_1(k7_relat_1(esk4_0,X1),esk1_0)), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 1.45/1.65  cnf(c_0_50, negated_conjecture, (~r1_tarski(k7_relat_1(esk4_0,esk2_0),k7_relat_1(k7_relat_1(esk4_0,esk2_0),X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.45/1.65  cnf(c_0_51, negated_conjecture, (k7_relat_1(k7_relat_1(esk4_0,X1),esk1_0)=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_36])])).
% 1.45/1.65  cnf(c_0_52, negated_conjecture, (~r1_tarski(k7_relat_1(esk4_0,esk2_0),k7_relat_1(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.45/1.65  cnf(c_0_53, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_42, c_0_51])).
% 1.45/1.65  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])]), ['proof']).
% 1.45/1.65  # SZS output end CNFRefutation
% 1.45/1.65  # Proof object total steps             : 55
% 1.45/1.65  # Proof object clause steps            : 34
% 1.45/1.65  # Proof object formula steps           : 21
% 1.45/1.65  # Proof object conjectures             : 25
% 1.45/1.65  # Proof object clause conjectures      : 22
% 1.45/1.65  # Proof object formula conjectures     : 3
% 1.45/1.65  # Proof object initial clauses used    : 12
% 1.45/1.65  # Proof object initial formulas used   : 10
% 1.45/1.65  # Proof object generating inferences   : 20
% 1.45/1.65  # Proof object simplifying inferences  : 8
% 1.45/1.65  # Training examples: 0 positive, 0 negative
% 1.45/1.65  # Parsed axioms                        : 11
% 1.45/1.65  # Removed by relevancy pruning/SinE    : 0
% 1.45/1.65  # Initial clauses                      : 16
% 1.45/1.65  # Removed in clause preprocessing      : 0
% 1.45/1.65  # Initial clauses in saturation        : 16
% 1.45/1.65  # Processed clauses                    : 293
% 1.45/1.65  # ...of these trivial                  : 8
% 1.45/1.65  # ...subsumed                          : 93
% 1.45/1.65  # ...remaining for further processing  : 192
% 1.45/1.65  # Other redundant clauses eliminated   : 0
% 1.45/1.65  # Clauses deleted for lack of memory   : 0
% 1.45/1.65  # Backward-subsumed                    : 3
% 1.45/1.65  # Backward-rewritten                   : 2
% 1.45/1.65  # Generated clauses                    : 765
% 1.45/1.65  # ...of the previous two non-trivial   : 641
% 1.45/1.65  # Contextual simplify-reflections      : 6
% 1.45/1.65  # Paramodulations                      : 765
% 1.45/1.65  # Factorizations                       : 0
% 1.45/1.65  # Equation resolutions                 : 0
% 1.45/1.65  # Propositional unsat checks           : 0
% 1.45/1.65  #    Propositional check models        : 0
% 1.45/1.65  #    Propositional check unsatisfiable : 0
% 1.45/1.65  #    Propositional clauses             : 0
% 1.45/1.65  #    Propositional clauses after purity: 0
% 1.45/1.65  #    Propositional unsat core size     : 0
% 1.45/1.65  #    Propositional preprocessing time  : 0.000
% 1.45/1.65  #    Propositional encoding time       : 0.000
% 1.45/1.65  #    Propositional solver time         : 0.000
% 1.45/1.65  #    Success case prop preproc time    : 0.000
% 1.45/1.65  #    Success case prop encoding time   : 0.000
% 1.45/1.65  #    Success case prop solver time     : 0.000
% 1.45/1.65  # Current number of processed clauses  : 171
% 1.45/1.65  #    Positive orientable unit clauses  : 37
% 1.45/1.65  #    Positive unorientable unit clauses: 0
% 1.45/1.65  #    Negative unit clauses             : 6
% 1.45/1.65  #    Non-unit-clauses                  : 128
% 1.45/1.65  # Current number of unprocessed clauses: 378
% 1.45/1.65  # ...number of literals in the above   : 3899
% 1.45/1.65  # Current number of archived formulas  : 0
% 1.45/1.65  # Current number of archived clauses   : 21
% 1.45/1.65  # Clause-clause subsumption calls (NU) : 75420
% 1.45/1.65  # Rec. Clause-clause subsumption calls : 70213
% 1.45/1.65  # Non-unit clause-clause subsumptions  : 90
% 1.45/1.65  # Unit Clause-clause subsumption calls : 468
% 1.45/1.65  # Rewrite failures with RHS unbound    : 0
% 1.45/1.65  # BW rewrite match attempts            : 15
% 1.45/1.65  # BW rewrite match successes           : 2
% 1.45/1.65  # Condensation attempts                : 0
% 1.45/1.65  # Condensation successes               : 0
% 1.45/1.65  # Termbank termtop insertions          : 27800
% 1.45/1.65  
% 1.45/1.65  # -------------------------------------------------
% 1.45/1.65  # User time                : 1.311 s
% 1.45/1.65  # System time              : 0.008 s
% 1.45/1.65  # Total time               : 1.319 s
% 1.45/1.65  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
