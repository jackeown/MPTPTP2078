%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t53_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:47 EDT 2019

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  138 (6336 expanded)
%              Number of clauses        :  100 (2556 expanded)
%              Number of leaves         :   19 (1490 expanded)
%              Depth                    :   19
%              Number of atoms          :  328 (31774 expanded)
%              Number of equality atoms :   87 (7398 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_funct_2,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ( v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X6] :
          ( ( v1_funct_1(X6)
            & v1_funct_2(X6,X2,X3)
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( ( X3 = k1_xboole_0
             => X2 = k1_xboole_0 )
           => r1_tarski(k8_relset_1(X1,X2,X5,X4),k8_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X5,X6),k7_relset_1(X2,X3,X6,X4))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t53_funct_2)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k8_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k1_partfun1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k7_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',dt_k1_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k2_relset_1)).

fof(t160_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(k2_relat_1(X2),k1_relat_1(X3))
           => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(k5_relat_1(X2,X3),k9_relat_1(X3,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t160_funct_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',d1_funct_2)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',dt_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t3_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',dt_k7_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',existence_m1_subset_1)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',dt_k8_relset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',dt_o_0_0_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( v1_funct_1(X5)
          & v1_funct_2(X5,X1,X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X6] :
            ( ( v1_funct_1(X6)
              & v1_funct_2(X6,X2,X3)
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ( ( X3 = k1_xboole_0
               => X2 = k1_xboole_0 )
             => r1_tarski(k8_relset_1(X1,X2,X5,X4),k8_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X5,X6),k7_relset_1(X2,X3,X6,X4))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_funct_2])).

fof(c_0_20,plain,(
    ! [X58,X59,X60,X61] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | k8_relset_1(X58,X59,X60,X61) = k10_relat_1(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk1_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk2_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ~ r1_tarski(k8_relset_1(esk1_0,esk2_0,esk5_0,esk4_0),k8_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk5_0,esk6_0),k7_relset_1(esk2_0,esk3_0,esk6_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ~ v1_funct_1(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k1_partfun1(X42,X43,X44,X45,X46,X47) = k5_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_23,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X54,X55,X56,X57] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k7_relset_1(X54,X55,X56,X57) = k9_relat_1(X56,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_26,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( v1_funct_1(k1_partfun1(X18,X19,X20,X21,X22,X23))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(k1_partfun1(X18,X19,X20,X21,X22,X23),k1_zfmisc_1(k2_zfmisc_1(X18,X21)))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_27,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_relset_1(X48,X49,X50) = k1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_31,plain,(
    ! [X82,X83,X84] :
      ( ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))
      | v1_relat_1(X84) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_32,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k2_relset_1(X51,X52,X53) = k2_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k8_relset_1(esk1_0,esk2_0,esk5_0,esk4_0),k8_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk5_0,esk6_0),k7_relset_1(esk2_0,esk3_0,esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk5_0,X1) = k10_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk6_0) = k5_relat_1(X3,esk6_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_39,plain,(
    ! [X62,X63,X64] :
      ( ~ v1_relat_1(X63)
      | ~ v1_relat_1(X64)
      | ~ r1_tarski(k2_relat_1(X63),k1_relat_1(X64))
      | r1_tarski(k10_relat_1(X63,X62),k10_relat_1(k5_relat_1(X63,X64),k9_relat_1(X64,X62))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_funct_1])])])).

cnf(c_0_40,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X17 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != k1_xboole_0
        | v1_funct_2(X17,X15,X16)
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_43,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k2_relset_1(X27,X28,X29),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_44,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,esk4_0),k8_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk5_0,esk6_0),k7_relset_1(esk2_0,esk3_0,esk6_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k7_relset_1(esk2_0,esk3_0,esk6_0,X1) = k9_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_29])])).

cnf(c_0_48,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk5_0,esk6_0) = k5_relat_1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_38])])).

cnf(c_0_49,plain,
    ( r1_tarski(k10_relat_1(X1,X3),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_relset_1(esk2_0,esk3_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_52,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk6_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_54,plain,(
    ! [X69,X70] :
      ( ( ~ m1_subset_1(X69,k1_zfmisc_1(X70))
        | r1_tarski(X69,X70) )
      & ( ~ r1_tarski(X69,X70)
        | m1_subset_1(X69,k1_zfmisc_1(X70)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_24])).

fof(c_0_57,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | m1_subset_1(k7_relset_1(X32,X33,X34,X35),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,esk4_0),k8_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk5_0,esk6_0),k9_relat_1(esk6_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_48]),c_0_38])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(k5_relat_1(X1,esk6_0),k9_relat_1(esk6_0,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_relset_1(esk2_0,esk3_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_61,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk6_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_28])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk5_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_24]),c_0_56])).

fof(c_0_64,plain,(
    ! [X74,X75,X76] :
      ( ~ r2_hidden(X74,X75)
      | ~ m1_subset_1(X75,k1_zfmisc_1(X76))
      | ~ v1_xboole_0(X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_65,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_66,plain,(
    ! [X67,X68] :
      ( ~ m1_subset_1(X67,X68)
      | v1_xboole_0(X68)
      | r2_hidden(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_67,plain,(
    ! [X40] : m1_subset_1(esk7_1(X40),X40) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_68,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | m1_subset_1(k8_relset_1(X36,X37,X38,X39),k1_zfmisc_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,esk4_0),k8_relset_1(esk1_0,esk3_0,k5_relat_1(esk5_0,esk6_0),k9_relat_1(esk6_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_70,negated_conjecture,
    ( k8_relset_1(esk1_0,esk3_0,k5_relat_1(esk5_0,esk6_0),X1) = k10_relat_1(k5_relat_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(k10_relat_1(X1,X2),k10_relat_1(k5_relat_1(X1,esk6_0),k9_relat_1(esk6_0,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k7_relset_1(esk2_0,esk3_0,esk6_0,X1),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_28])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_78,plain,(
    ! [X77] :
      ( ~ v1_xboole_0(X77)
      | X77 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_79,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,esk4_0),k10_relat_1(k5_relat_1(esk5_0,esk6_0),k9_relat_1(esk6_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(k10_relat_1(esk5_0,X1),k10_relat_1(k5_relat_1(esk5_0,esk6_0),k9_relat_1(esk6_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,k7_relset_1(esk2_0,esk3_0,esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k8_relset_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_24])).

cnf(c_0_87,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(k7_relset_1(esk2_0,esk3_0,esk6_0,X1))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,k8_relset_1(esk1_0,esk2_0,esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_86])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(esk5_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k8_relset_1(esk1_0,esk3_0,k5_relat_1(esk5_0,esk6_0),X1),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_59])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(k9_relat_1(esk6_0,X1))
    | ~ v1_xboole_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_46])).

cnf(c_0_97,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(k8_relset_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_83])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_2(X2,X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_2(esk5_0,esk1_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,k8_relset_1(esk1_0,esk3_0,k5_relat_1(esk5_0,esk6_0),X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_95])).

cnf(c_0_103,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk7_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_77])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(k9_relat_1(esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_88]),c_0_97])])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(k10_relat_1(esk5_0,X1))
    | ~ v1_xboole_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_34])).

cnf(c_0_106,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])])).

cnf(c_0_107,negated_conjecture,
    ( v1_xboole_0(k8_relset_1(esk1_0,esk3_0,k5_relat_1(esk5_0,esk6_0),X1))
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_83])).

cnf(c_0_108,plain,
    ( v1_xboole_0(esk7_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_83])).

cnf(c_0_109,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_63])).

cnf(c_0_111,negated_conjecture,
    ( k9_relat_1(esk6_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_104])).

cnf(c_0_112,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_xboole_0(k10_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_97])])).

cnf(c_0_113,negated_conjecture,
    ( v1_xboole_0(k10_relat_1(k5_relat_1(esk5_0,esk6_0),X1))
    | ~ v1_xboole_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_107,c_0_70])).

cnf(c_0_114,plain,
    ( esk7_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_108])).

cnf(c_0_115,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X2,k1_xboole_0,X1) ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_88]),c_0_94])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_88]),c_0_94])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk5_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_83])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,esk4_0),k10_relat_1(k5_relat_1(esk5_0,esk6_0),k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( k10_relat_1(esk5_0,X1) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_112])).

cnf(c_0_121,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_xboole_0(k10_relat_1(k5_relat_1(esk5_0,esk6_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_106]),c_0_97])])).

cnf(c_0_122,plain,
    ( r1_tarski(esk7_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_77])).

cnf(c_0_123,plain,
    ( esk7_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_97])).

cnf(c_0_124,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_94]),c_0_97])])).

cnf(c_0_126,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k10_relat_1(k5_relat_1(esk5_0,esk6_0),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk5_0,esk6_0),X1) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_121])).

cnf(c_0_128,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_88]),c_0_94]),c_0_124])).

cnf(c_0_130,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128])])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(k5_relat_1(X1,esk6_0),k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_129]),c_0_51])]),c_0_111])).

cnf(c_0_133,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(k1_xboole_0,esk4_0),k10_relat_1(k5_relat_1(k1_xboole_0,esk6_0),k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_131]),c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k10_relat_1(k1_xboole_0,X1),k10_relat_1(k5_relat_1(k1_xboole_0,esk6_0),k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_134]),c_0_128])])).

cnf(c_0_137,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136])]),
    [proof]).
%------------------------------------------------------------------------------
