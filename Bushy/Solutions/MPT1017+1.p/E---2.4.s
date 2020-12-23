%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t83_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:50 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  66 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  103 ( 378 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X1,X1,X2) = X1 )
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t83_funct_2.p',t83_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t83_funct_2.p',d3_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t83_funct_2.p',redefinition_k2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t83_funct_2.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t83_funct_2.p',cc1_relset_1)).

fof(cc3_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) )
       => ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t83_funct_2.p',cc3_funct_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( ( v2_funct_1(X2)
            & k2_relset_1(X1,X1,X2) = X1 )
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,X1,X1)
            & v3_funct_2(X2,X1,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t83_funct_2])).

fof(c_0_7,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v2_funct_1(esk2_0)
    & k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,esk1_0,esk1_0)
      | ~ v3_funct_2(esk2_0,esk1_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X8,X9] :
      ( ( ~ v2_funct_2(X9,X8)
        | k2_relat_1(X9) = X8
        | ~ v1_relat_1(X9)
        | ~ v5_relat_1(X9,X8) )
      & ( k2_relat_1(X9) != X8
        | v2_funct_2(X9,X8)
        | ~ v1_relat_1(X9)
        | ~ v5_relat_1(X9,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k2_relset_1(X15,X16,X17) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_10,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_11,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,plain,(
    ! [X41,X42,X43] :
      ( ( v1_funct_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X43)
        | ~ v2_funct_2(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v3_funct_2(X43,X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X43)
        | ~ v2_funct_2(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_2])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,esk1_0,esk1_0)
    | ~ v3_funct_2(esk2_0,esk1_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( v3_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( ~ v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_25,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_funct_2(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_23]),c_0_14])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
