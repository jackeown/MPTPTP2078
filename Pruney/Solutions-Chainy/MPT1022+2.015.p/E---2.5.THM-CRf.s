%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 839 expanded)
%              Number of clauses        :   67 ( 303 expanded)
%              Number of leaves         :   19 ( 215 expanded)
%              Depth                    :   14
%              Number of atoms          :  320 (3753 expanded)
%              Number of equality atoms :   63 ( 770 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t92_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X1)
        & v3_funct_2(X3,X1,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r1_tarski(X2,X1)
       => ( k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2)) = X2
          & k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

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

fof(t154_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(dt_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k2_funct_2(X1,X2))
        & v1_funct_2(k2_funct_2(X1,X2),X1,X1)
        & v3_funct_2(k2_funct_2(X1,X2),X1,X1)
        & m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t164_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X1)
          & v3_funct_2(X3,X1,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r1_tarski(X2,X1)
         => ( k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2)) = X2
            & k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t92_funct_2])).

fof(c_0_20,plain,(
    ! [X44,X45] :
      ( ~ v1_funct_1(X45)
      | ~ v1_funct_2(X45,X44,X44)
      | ~ v3_funct_2(X45,X44,X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))
      | k2_funct_2(X44,X45) = k2_funct_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & v3_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r1_tarski(esk2_0,esk1_0)
    & ( k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0
      | k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X37,X38,X39] :
      ( ( v1_funct_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v3_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v2_funct_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v3_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v2_funct_2(X39,X38)
        | ~ v1_funct_1(X39)
        | ~ v3_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_23,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v2_funct_1(X23)
      | k9_relat_1(X23,X22) = k10_relat_1(k2_funct_1(X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).

cnf(c_0_26,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v3_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X42,X43] :
      ( ( v1_funct_1(k2_funct_2(X42,X43))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X42,X42)
        | ~ v3_funct_2(X43,X42,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))) )
      & ( v1_funct_2(k2_funct_2(X42,X43),X42,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X42,X42)
        | ~ v3_funct_2(X43,X42,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))) )
      & ( v3_funct_2(k2_funct_2(X42,X43),X42,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X42,X42)
        | ~ v3_funct_2(X43,X42,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))) )
      & ( m1_subset_1(k2_funct_2(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X42,X42)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X42,X42)
        | ~ v3_funct_2(X43,X42,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | r1_tarski(k9_relat_1(X19,k10_relat_1(X19,X18)),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_36,plain,
    ( k9_relat_1(X1,X2) = k10_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_funct_2(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_33])])).

cnf(c_0_40,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_43,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k7_relset_1(X29,X30,X31,X32) = k9_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(k2_funct_2(esk1_0,esk3_0),X1) = k9_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_30]),c_0_39])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_47,plain,
    ( v1_relat_1(k2_funct_2(X1,X2))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_41]),c_0_33])])).

fof(c_0_48,plain,(
    ! [X40,X41] :
      ( ( ~ v2_funct_2(X41,X40)
        | k2_relat_1(X41) = X40
        | ~ v1_relat_1(X41)
        | ~ v5_relat_1(X41,X40) )
      & ( k2_relat_1(X41) != X40
        | v2_funct_2(X41,X40)
        | ~ v1_relat_1(X41)
        | ~ v5_relat_1(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_49,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0
    | k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_53,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k8_relset_1(X33,X34,X35,X36) = k10_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k9_relat_1(k2_funct_2(esk1_0,esk3_0),k9_relat_1(esk3_0,X1)),X1)
    | ~ v1_relat_1(k2_funct_2(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(k2_funct_2(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

fof(c_0_56,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ r1_tarski(X20,k2_relat_1(X21))
      | k9_relat_1(X21,k10_relat_1(X21,X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_57,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( v2_funct_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_29]),c_0_30])])).

cnf(c_0_59,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0
    | k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_27])])).

cnf(c_0_61,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k9_relat_1(k2_funct_2(esk1_0,esk3_0),k9_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_63,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_39])])).

fof(c_0_65,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v4_relat_1(X17,X16)
      | X17 = k7_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_66,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_67,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0)) != esk2_0
    | k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_27])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k9_relat_1(k2_funct_2(esk1_0,esk3_0),X1),k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_30]),c_0_39]),c_0_64])])).

fof(c_0_69,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_70,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k2_relat_1(k7_relat_1(X14,X13)) = k9_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_71,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_27])).

fof(c_0_73,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_74,plain,
    ( v3_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0)) != esk2_0
    | k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_61]),c_0_27])])).

fof(c_0_76,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k10_relat_1(X15,k2_relat_1(X15)) = k1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))
    | ~ r1_tarski(X1,k2_relat_1(k2_funct_2(esk1_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_63]),c_0_45]),c_0_45]),c_0_46]),c_0_55])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_39])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( v2_funct_2(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_40]),c_0_74])).

cnf(c_0_83,plain,
    ( v5_relat_1(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_41])).

cnf(c_0_84,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) != esk2_0
    | k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_52]),c_0_27])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_86,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ r1_tarski(X24,k1_relat_1(X25))
      | ~ v2_funct_1(X25)
      | k10_relat_1(X25,k9_relat_1(X25,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).

cnf(c_0_87,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(k2_funct_2(esk1_0,esk3_0))))
    | ~ r1_tarski(k9_relat_1(esk3_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( k9_relat_1(esk3_0,esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_39])]),c_0_64])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_91,plain,
    ( k2_relat_1(k2_funct_2(X1,X2)) = X1
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_82]),c_0_47]),c_0_83])).

cnf(c_0_92,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_93,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_63]),c_0_30]),c_0_39]),c_0_64]),c_0_85])])).

cnf(c_0_94,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(esk3_0) = k10_relat_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_64]),c_0_39])])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_relat_1(k2_funct_2(esk1_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])])).

cnf(c_0_97,negated_conjecture,
    ( k2_relat_1(k2_funct_2(esk1_0,esk3_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_98,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k10_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_38]),c_0_30]),c_0_39]),c_0_95])])).

cnf(c_0_100,negated_conjecture,
    ( k10_relat_1(esk3_0,esk1_0) = esk1_0
    | ~ r1_tarski(esk1_0,k10_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_89]),c_0_38]),c_0_30]),c_0_39]),c_0_95])])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_102,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_78])).

cnf(c_0_103,negated_conjecture,
    ( k10_relat_1(esk3_0,esk1_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_85])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t92_funct_2, conjecture, ![X1, X2, X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_tarski(X2,X1)=>(k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2))=X2&k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 0.19/0.41  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.19/0.41  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.19/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.41  fof(t154_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k9_relat_1(X2,X1)=k10_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 0.19/0.41  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.19/0.41  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.19/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.41  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.41  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.19/0.41  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.19/0.41  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.19/0.41  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.19/0.41  fof(t164_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 0.19/0.41  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_tarski(X2,X1)=>(k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2))=X2&k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2))=X2)))), inference(assume_negation,[status(cth)],[t92_funct_2])).
% 0.19/0.41  fof(c_0_20, plain, ![X44, X45]:(~v1_funct_1(X45)|~v1_funct_2(X45,X44,X44)|~v3_funct_2(X45,X44,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))|k2_funct_2(X44,X45)=k2_funct_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.19/0.41  fof(c_0_21, negated_conjecture, ((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&v3_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(r1_tarski(esk2_0,esk1_0)&(k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.19/0.41  fof(c_0_22, plain, ![X37, X38, X39]:(((v1_funct_1(X39)|(~v1_funct_1(X39)|~v3_funct_2(X39,X37,X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v2_funct_1(X39)|(~v1_funct_1(X39)|~v3_funct_2(X39,X37,X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(v2_funct_2(X39,X38)|(~v1_funct_1(X39)|~v3_funct_2(X39,X37,X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.19/0.41  fof(c_0_23, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.41  fof(c_0_24, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.41  fof(c_0_25, plain, ![X22, X23]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v2_funct_1(X23)|k9_relat_1(X23,X22)=k10_relat_1(k2_funct_1(X23),X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).
% 0.19/0.41  cnf(c_0_26, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (v3_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_31, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_32, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_33, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  fof(c_0_34, plain, ![X42, X43]:((((v1_funct_1(k2_funct_2(X42,X43))|(~v1_funct_1(X43)|~v1_funct_2(X43,X42,X42)|~v3_funct_2(X43,X42,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42)))))&(v1_funct_2(k2_funct_2(X42,X43),X42,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,X42,X42)|~v3_funct_2(X43,X42,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))))))&(v3_funct_2(k2_funct_2(X42,X43),X42,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,X42,X42)|~v3_funct_2(X43,X42,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))))))&(m1_subset_1(k2_funct_2(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X42,X42)))|(~v1_funct_1(X43)|~v1_funct_2(X43,X42,X42)|~v3_funct_2(X43,X42,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.19/0.41  fof(c_0_35, plain, ![X18, X19]:(~v1_relat_1(X19)|~v1_funct_1(X19)|r1_tarski(k9_relat_1(X19,k10_relat_1(X19,X18)),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.19/0.41  cnf(c_0_36, plain, (k9_relat_1(X1,X2)=k10_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (k2_funct_1(esk3_0)=k2_funct_2(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_29]), c_0_30])])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_33])])).
% 0.19/0.41  cnf(c_0_40, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_41, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  fof(c_0_42, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.41  fof(c_0_43, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k7_relset_1(X29,X30,X31,X32)=k9_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.41  cnf(c_0_44, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (k10_relat_1(k2_funct_2(esk1_0,esk3_0),X1)=k9_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_30]), c_0_39])])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (v1_funct_1(k2_funct_2(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.19/0.41  cnf(c_0_47, plain, (v1_relat_1(k2_funct_2(X1,X2))|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_41]), c_0_33])])).
% 0.19/0.41  fof(c_0_48, plain, ![X40, X41]:((~v2_funct_2(X41,X40)|k2_relat_1(X41)=X40|(~v1_relat_1(X41)|~v5_relat_1(X41,X40)))&(k2_relat_1(X41)!=X40|v2_funct_2(X41,X40)|(~v1_relat_1(X41)|~v5_relat_1(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.19/0.41  cnf(c_0_49, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_50, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_52, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  fof(c_0_53, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k8_relset_1(X33,X34,X35,X36)=k10_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (r1_tarski(k9_relat_1(k2_funct_2(esk1_0,esk3_0),k9_relat_1(esk3_0,X1)),X1)|~v1_relat_1(k2_funct_2(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (v1_relat_1(k2_funct_2(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.19/0.41  fof(c_0_56, plain, ![X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~r1_tarski(X20,k2_relat_1(X21))|k9_relat_1(X21,k10_relat_1(X21,X20))=X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.19/0.41  cnf(c_0_57, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (v2_funct_2(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_29]), c_0_30])])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_50, c_0_27])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_27])])).
% 0.19/0.41  cnf(c_0_61, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r1_tarski(k9_relat_1(k2_funct_2(esk1_0,esk3_0),k9_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.19/0.41  cnf(c_0_63, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_39])])).
% 0.19/0.41  fof(c_0_65, plain, ![X16, X17]:(~v1_relat_1(X17)|~v4_relat_1(X17,X16)|X17=k7_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.19/0.41  cnf(c_0_66, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_27])])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (r1_tarski(k9_relat_1(k2_funct_2(esk1_0,esk3_0),X1),k10_relat_1(esk3_0,X1))|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_30]), c_0_39]), c_0_64])])).
% 0.19/0.41  fof(c_0_69, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  fof(c_0_70, plain, ![X13, X14]:(~v1_relat_1(X14)|k2_relat_1(k7_relat_1(X14,X13))=k9_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.41  cnf(c_0_71, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_66, c_0_27])).
% 0.19/0.41  fof(c_0_73, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  cnf(c_0_74, plain, (v3_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0))!=esk2_0|k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_61]), c_0_27])])).
% 0.19/0.41  fof(c_0_76, plain, ![X15]:(~v1_relat_1(X15)|k10_relat_1(X15,k2_relat_1(X15))=k1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))|~r1_tarski(X1,k2_relat_1(k2_funct_2(esk1_0,esk3_0)))|~r1_tarski(k9_relat_1(esk3_0,X1),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_63]), c_0_45]), c_0_45]), c_0_46]), c_0_55])])).
% 0.19/0.41  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.41  cnf(c_0_79, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (k7_relat_1(esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_39])])).
% 0.19/0.41  cnf(c_0_81, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.41  cnf(c_0_82, plain, (v2_funct_2(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_41]), c_0_40]), c_0_74])).
% 0.19/0.41  cnf(c_0_83, plain, (v5_relat_1(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_50, c_0_41])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))!=esk2_0|k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_52]), c_0_27])])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  fof(c_0_86, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(~r1_tarski(X24,k1_relat_1(X25))|~v2_funct_1(X25)|k10_relat_1(X25,k9_relat_1(X25,X24))=X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).
% 0.19/0.41  cnf(c_0_87, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))|~m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(k2_funct_2(esk1_0,esk3_0))))|~r1_tarski(k9_relat_1(esk3_0,X1),esk1_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, (k9_relat_1(esk3_0,esk1_0)=esk1_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_39])]), c_0_64])).
% 0.19/0.41  cnf(c_0_90, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_81])).
% 0.19/0.41  cnf(c_0_91, plain, (k2_relat_1(k2_funct_2(X1,X2))=X1|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_82]), c_0_47]), c_0_83])).
% 0.19/0.41  cnf(c_0_92, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.41  cnf(c_0_93, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_63]), c_0_30]), c_0_39]), c_0_64]), c_0_85])])).
% 0.19/0.41  cnf(c_0_94, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.41  cnf(c_0_95, negated_conjecture, (k1_relat_1(esk3_0)=k10_relat_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_64]), c_0_39])])).
% 0.19/0.41  cnf(c_0_96, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_relat_1(k2_funct_2(esk1_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (k2_relat_1(k2_funct_2(esk1_0,esk3_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.19/0.41  cnf(c_0_98, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_92, c_0_90])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (~r1_tarski(esk2_0,k10_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_38]), c_0_30]), c_0_39]), c_0_95])])).
% 0.19/0.41  cnf(c_0_100, negated_conjecture, (k10_relat_1(esk3_0,esk1_0)=esk1_0|~r1_tarski(esk1_0,k10_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_89]), c_0_38]), c_0_30]), c_0_39]), c_0_95])])).
% 0.19/0.41  cnf(c_0_101, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 0.19/0.41  cnf(c_0_102, negated_conjecture, (~m1_subset_1(esk2_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk1_0)))), inference(spm,[status(thm)],[c_0_99, c_0_78])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (k10_relat_1(esk3_0,esk1_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])])).
% 0.19/0.41  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_92, c_0_85])).
% 0.19/0.41  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_104])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 106
% 0.19/0.41  # Proof object clause steps            : 67
% 0.19/0.41  # Proof object formula steps           : 39
% 0.19/0.41  # Proof object conjectures             : 41
% 0.19/0.41  # Proof object clause conjectures      : 38
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 29
% 0.19/0.41  # Proof object initial formulas used   : 19
% 0.19/0.41  # Proof object generating inferences   : 33
% 0.19/0.41  # Proof object simplifying inferences  : 91
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 19
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 34
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 33
% 0.19/0.41  # Processed clauses                    : 377
% 0.19/0.41  # ...of these trivial                  : 12
% 0.19/0.41  # ...subsumed                          : 121
% 0.19/0.41  # ...remaining for further processing  : 244
% 0.19/0.41  # Other redundant clauses eliminated   : 3
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 59
% 0.19/0.41  # Generated clauses                    : 749
% 0.19/0.41  # ...of the previous two non-trivial   : 656
% 0.19/0.41  # Contextual simplify-reflections      : 12
% 0.19/0.41  # Paramodulations                      : 746
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 3
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 150
% 0.19/0.41  #    Positive orientable unit clauses  : 37
% 0.19/0.41  #    Positive unorientable unit clauses: 1
% 0.19/0.41  #    Negative unit clauses             : 1
% 0.19/0.41  #    Non-unit-clauses                  : 111
% 0.19/0.41  # Current number of unprocessed clauses: 326
% 0.19/0.41  # ...number of literals in the above   : 1768
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 91
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 4052
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1745
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 129
% 0.19/0.41  # Unit Clause-clause subsumption calls : 78
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 11
% 0.19/0.41  # BW rewrite match successes           : 4
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 22508
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.058 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.064 s
% 0.19/0.41  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
