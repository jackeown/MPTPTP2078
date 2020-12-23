%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t171_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 109 expanded)
%              Number of clauses        :   30 (  46 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :  166 ( 258 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t162_funct_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t162_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',redefinition_k6_partfun1)).

fof(t171_funct_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t171_funct_2)).

fof(cc4_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( ( v1_relat_2(X2)
          & v1_funct_1(X2)
          & v1_partfun1(X2,X1)
          & v1_funct_2(X2,X1,X1) )
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',cc4_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',cc1_funct_2)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',fc3_funct_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',redefinition_k7_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',dt_k6_partfun1)).

fof(fc3_partfun1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v3_relat_2(k6_relat_1(X1))
      & v4_relat_2(k6_relat_1(X1))
      & v8_relat_2(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',fc3_partfun1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',dt_k6_relat_1)).

fof(cc3_partfun1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v3_relat_2(X1)
        & v8_relat_2(X1) )
     => ( v1_relat_1(X1)
        & v1_relat_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',cc3_partfun1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t3_subset)).

fof(t92_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X1)
        & v3_funct_2(X3,X1,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r1_tarski(X2,X1)
       => ( k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2)) = X2
          & k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t171_funct_2.p',t92_funct_2)).

fof(c_0_13,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k9_relat_1(k6_relat_1(X30),X31) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_funct_1])])).

fof(c_0_14,plain,(
    ! [X21] : k6_partfun1(X21) = k6_relat_1(X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t171_funct_2])).

fof(c_0_16,plain,(
    ! [X56,X57] :
      ( ( v1_funct_1(X57)
        | ~ v1_relat_2(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_partfun1(X57,X56)
        | ~ v1_funct_2(X57,X56,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X56,X56))) )
      & ( v1_funct_2(X57,X56,X56)
        | ~ v1_relat_2(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_partfun1(X57,X56)
        | ~ v1_funct_2(X57,X56,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X56,X56))) )
      & ( v3_funct_2(X57,X56,X56)
        | ~ v1_relat_2(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_partfun1(X57,X56)
        | ~ v1_funct_2(X57,X56,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X56,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_funct_2])])])).

fof(c_0_17,plain,(
    ! [X52,X53,X54] :
      ( ( v1_funct_1(X54)
        | ~ v1_funct_1(X54)
        | ~ v1_partfun1(X54,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( v1_funct_2(X54,X52,X53)
        | ~ v1_funct_1(X54)
        | ~ v1_partfun1(X54,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_18,plain,(
    ! [X58] :
      ( v1_relat_1(k6_relat_1(X58))
      & v1_funct_1(k6_relat_1(X58)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_19,plain,
    ( k9_relat_1(k6_relat_1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k7_relset_1(X22,X23,X24,X25) = k9_relat_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_23,plain,(
    ! [X9] :
      ( v1_partfun1(k6_partfun1(X9),X9)
      & m1_subset_1(k6_partfun1(X9),k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_24,plain,
    ( v3_funct_2(X1,X2,X2)
    | ~ v1_relat_2(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X59] :
      ( v1_relat_1(k6_relat_1(X59))
      & v3_relat_2(k6_relat_1(X59))
      & v4_relat_2(k6_relat_1(X59))
      & v8_relat_2(k6_relat_1(X59)) ) ),
    inference(variable_rename,[status(thm)],[fc3_partfun1])).

fof(c_0_28,plain,(
    ! [X10] : v1_relat_1(k6_relat_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_29,plain,
    ( k9_relat_1(k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v3_funct_2(X1,X2,X2)
    | ~ v1_relat_2(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( v1_funct_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_35,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X55] :
      ( ( v1_relat_1(X55)
        | ~ v1_relat_1(X55)
        | ~ v3_relat_2(X55)
        | ~ v8_relat_2(X55) )
      & ( v1_relat_2(X55)
        | ~ v1_relat_1(X55)
        | ~ v3_relat_2(X55)
        | ~ v8_relat_2(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_partfun1])])])).

cnf(c_0_37,plain,
    ( v8_relat_2(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v3_relat_2(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X36,k1_zfmisc_1(X37))
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | m1_subset_1(X36,k1_zfmisc_1(X37)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,plain,(
    ! [X49,X50,X51] :
      ( ( k7_relset_1(X49,X49,X51,k8_relset_1(X49,X49,X51,X50)) = X50
        | ~ r1_tarski(X50,X49)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X49)
        | ~ v3_funct_2(X51,X49,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X49))) )
      & ( k8_relset_1(X49,X49,X51,k7_relset_1(X49,X49,X51,X50)) = X50
        | ~ r1_tarski(X50,X49)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X49)
        | ~ v3_funct_2(X51,X49,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_funct_2])])])).

cnf(c_0_42,negated_conjecture,
    ( k9_relat_1(k6_partfun1(esk1_0),esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,plain,
    ( k9_relat_1(k6_partfun1(X1),X2) = k7_relset_1(X1,X1,k6_partfun1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,plain,
    ( v3_funct_2(k6_partfun1(X1),X1,X1)
    | ~ v1_relat_2(k6_partfun1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_34]),c_0_35])])).

cnf(c_0_45,plain,
    ( v1_relat_2(X1)
    | ~ v1_relat_1(X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( v8_relat_2(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_47,plain,
    ( v3_relat_2(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_48,plain,
    ( v1_relat_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_20])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k8_relset_1(X1,X1,X2,k7_relset_1(X1,X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( v3_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_53,plain,
    ( v1_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_32]),c_0_34]),c_0_35])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_34]),c_0_54]),c_0_32])]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
