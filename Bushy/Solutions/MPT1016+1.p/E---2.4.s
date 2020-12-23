%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t77_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:49 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 407 expanded)
%              Number of clauses        :   29 ( 142 expanded)
%              Number of leaves         :    5 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 (2822 expanded)
%              Number of equality atoms :   37 ( 697 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',t77_funct_2)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',t67_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',cc1_relset_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',d8_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_funct_2])).

fof(c_0_6,plain,(
    ! [X38,X39] :
      ( ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,X38,X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X38)))
      | k1_relset_1(X38,X38,X39) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_7,negated_conjecture,(
    ! [X9,X10] :
      ( v1_funct_1(esk2_0)
      & v1_funct_2(esk2_0,esk1_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
      & ( r2_hidden(esk3_0,esk1_0)
        | ~ v2_funct_1(esk2_0) )
      & ( r2_hidden(esk4_0,esk1_0)
        | ~ v2_funct_1(esk2_0) )
      & ( k1_funct_1(esk2_0,esk3_0) = k1_funct_1(esk2_0,esk4_0)
        | ~ v2_funct_1(esk2_0) )
      & ( esk3_0 != esk4_0
        | ~ v2_funct_1(esk2_0) )
      & ( v2_funct_1(esk2_0)
        | ~ r2_hidden(X9,esk1_0)
        | ~ r2_hidden(X10,esk1_0)
        | k1_funct_1(esk2_0,X9) != k1_funct_1(esk2_0,X10)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_9,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | v1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v2_funct_1(X13)
        | ~ r2_hidden(X14,k1_relat_1(X13))
        | ~ r2_hidden(X15,k1_relat_1(X13))
        | k1_funct_1(X13,X14) != k1_funct_1(X13,X15)
        | X14 = X15
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk5_1(X13),k1_relat_1(X13))
        | v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk6_1(X13),k1_relat_1(X13))
        | v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk5_1(X13)) = k1_funct_1(X13,esk6_1(X13))
        | v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( esk5_1(X13) != esk6_1(X13)
        | v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_15,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_10]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v2_funct_1(esk2_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X2,esk1_0)
    | k1_funct_1(esk2_0,X1) != k1_funct_1(esk2_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk2_0,X1) != k1_funct_1(esk2_0,X2)
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_12])]),c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_0) = k1_funct_1(esk2_0,esk4_0)
    | ~ v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0)
    | ~ v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( r2_hidden(esk5_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk4_0
    | k1_funct_1(esk2_0,X1) != k1_funct_1(esk2_0,esk3_0)
    | ~ r2_hidden(X1,esk1_0)
    | ~ v2_funct_1(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0)
    | ~ v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( esk3_0 != esk4_0
    | ~ v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_1(esk2_0),esk1_0)
    | v2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_20]),c_0_12])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_funct_1(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(esk6_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( k1_funct_1(X1,esk5_1(X1)) = k1_funct_1(X1,esk6_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_1(esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_1(esk2_0),esk1_0)
    | v2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_12])])).

cnf(c_0_35,negated_conjecture,
    ( X1 = esk5_1(esk2_0)
    | k1_funct_1(esk2_0,X1) != k1_funct_1(esk2_0,esk6_1(esk2_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_20]),c_0_12])]),c_0_33])]),c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_1(esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_37,plain,
    ( v2_funct_1(X1)
    | esk5_1(X1) != esk6_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( esk5_1(esk2_0) = esk6_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20]),c_0_12])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
