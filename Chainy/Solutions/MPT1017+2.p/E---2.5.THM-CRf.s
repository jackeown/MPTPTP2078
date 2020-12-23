%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1017+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:00 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   34 (  69 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 384 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(cc3_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) )
       => ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_2)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X3352,X3353] :
      ( ( ~ v2_funct_2(X3353,X3352)
        | k2_relat_1(X3353) = X3352
        | ~ v1_relat_1(X3353)
        | ~ v5_relat_1(X3353,X3352) )
      & ( k2_relat_1(X3353) != X3352
        | v2_funct_2(X3353,X3352)
        | ~ v1_relat_1(X3353)
        | ~ v5_relat_1(X3353,X3352) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_9,plain,(
    ! [X897,X898,X899] :
      ( ~ m1_subset_1(X899,k1_zfmisc_1(k2_zfmisc_1(X897,X898)))
      | k2_relset_1(X897,X898,X899) = k2_relat_1(X899) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v2_funct_1(esk2_0)
    & k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,esk1_0,esk1_0)
      | ~ v3_funct_2(esk2_0,esk1_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X3388,X3389,X3390] :
      ( ( v4_relat_1(X3390,X3388)
        | ~ m1_subset_1(X3390,k1_zfmisc_1(k2_zfmisc_1(X3388,X3389))) )
      & ( v5_relat_1(X3390,X3389)
        | ~ m1_subset_1(X3390,k1_zfmisc_1(k2_zfmisc_1(X3388,X3389))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_12,plain,(
    ! [X77,X78] :
      ( ~ v1_relat_1(X77)
      | ~ m1_subset_1(X78,k1_zfmisc_1(X77))
      | v1_relat_1(X78) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,plain,(
    ! [X388,X389] : v1_relat_1(k2_zfmisc_1(X388,X389)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_14,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X414,X415,X416] :
      ( ( v1_funct_1(X416)
        | ~ v1_funct_1(X416)
        | ~ v2_funct_1(X416)
        | ~ v2_funct_2(X416,X415)
        | ~ m1_subset_1(X416,k1_zfmisc_1(k2_zfmisc_1(X414,X415))) )
      & ( v3_funct_2(X416,X414,X415)
        | ~ v1_funct_1(X416)
        | ~ v2_funct_1(X416)
        | ~ v2_funct_2(X416,X415)
        | ~ m1_subset_1(X416,k1_zfmisc_1(k2_zfmisc_1(X414,X415))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_2])])])).

cnf(c_0_22,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,esk1_0,esk1_0)
    | ~ v3_funct_2(esk2_0,esk1_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( v3_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( ~ v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_16])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_30]),c_0_31]),c_0_27])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
