%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 154 expanded)
%              Number of clauses        :   35 (  54 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 877 expanded)
%              Number of equality atoms :   41 (  51 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
              & v2_funct_1(X2) )
           => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(t50_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = X1
              & k1_relat_1(X3) = X1
              & r1_tarski(k2_relat_1(X3),X1)
              & v2_funct_1(X2)
              & k5_relat_1(X3,X2) = X2 )
           => X3 = k6_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
                & v2_funct_1(X2) )
             => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_funct_2])).

fof(c_0_12,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ r2_relset_1(X21,X22,X23,X24)
        | X23 = X24
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X23 != X24
        | r2_relset_1(X21,X22,X23,X24)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_14,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( v1_funct_1(k1_partfun1(X25,X26,X27,X28,X29,X30))
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( m1_subset_1(k1_partfun1(X25,X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X25,X28)))
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,X38,X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X38)))
      | k1_relset_1(X38,X38,X39) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_20,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | k1_relat_1(X10) != X9
      | k1_relat_1(X11) != X9
      | ~ r1_tarski(k2_relat_1(X11),X9)
      | ~ v2_funct_1(X10)
      | k5_relat_1(X11,X10) != X10
      | X11 = k6_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_funct_1])])])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( ~ v5_relat_1(X8,X7)
        | r1_tarski(k2_relat_1(X8),X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r1_tarski(k2_relat_1(X8),X7)
        | v5_relat_1(X8,X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_22,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ v1_funct_1(X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_partfun1(X31,X32,X33,X34,X35,X36) = k5_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_23,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = esk2_0
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_31,plain,(
    ! [X37] : k6_partfun1(X37) = k6_relat_1(X37) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_32,plain,
    ( X2 = k6_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != X3
    | k1_relat_1(X2) != X3
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X2,X1) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_16]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_36,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( X1 = k6_relat_1(X2)
    | k5_relat_1(X1,X3) != X3
    | k1_relat_1(X1) != X2
    | k1_relat_1(X3) != X2
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k5_relat_1(esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_16]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25]),c_0_27])])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_38]),c_0_16]),c_0_26])])).

cnf(c_0_47,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_50,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k6_relat_1(X1) = esk3_0
    | esk1_0 != X1
    | ~ v5_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_27]),c_0_26]),c_0_48]),c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_54,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_56,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.036 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 0.13/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.13/0.39  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.13/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.39  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 0.13/0.39  fof(t50_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 0.13/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.39  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.13/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.13/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.13/0.39  fof(c_0_12, plain, ![X21, X22, X23, X24]:((~r2_relset_1(X21,X22,X23,X24)|X23=X24|(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&(X23!=X24|r2_relset_1(X21,X22,X23,X24)|(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.13/0.39  fof(c_0_13, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)&v2_funct_1(esk2_0))&~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.39  cnf(c_0_14, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_17, plain, ![X25, X26, X27, X28, X29, X30]:((v1_funct_1(k1_partfun1(X25,X26,X27,X28,X29,X30))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&(m1_subset_1(k1_partfun1(X25,X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X25,X28)))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.39  fof(c_0_19, plain, ![X38, X39]:(~v1_funct_1(X39)|~v1_funct_2(X39,X38,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X38)))|k1_relset_1(X38,X38,X39)=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.13/0.39  fof(c_0_20, plain, ![X9, X10, X11]:(~v1_relat_1(X10)|~v1_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11)|(k1_relat_1(X10)!=X9|k1_relat_1(X11)!=X9|~r1_tarski(k2_relat_1(X11),X9)|~v2_funct_1(X10)|k5_relat_1(X11,X10)!=X10|X11=k6_relat_1(X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_funct_1])])])).
% 0.13/0.39  fof(c_0_21, plain, ![X7, X8]:((~v5_relat_1(X8,X7)|r1_tarski(k2_relat_1(X8),X7)|~v1_relat_1(X8))&(~r1_tarski(k2_relat_1(X8),X7)|v5_relat_1(X8,X7)|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.39  fof(c_0_22, plain, ![X31, X32, X33, X34, X35, X36]:(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_partfun1(X31,X32,X33,X34,X35,X36)=k5_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)=esk2_0|~m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.13/0.39  cnf(c_0_24, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_29, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_30, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.39  fof(c_0_31, plain, ![X37]:k6_partfun1(X37)=k6_relat_1(X37), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.13/0.39  cnf(c_0_32, plain, (X2=k6_relat_1(X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=X3|k1_relat_1(X2)!=X3|~r1_tarski(k2_relat_1(X2),X3)|~v2_funct_1(X1)|k5_relat_1(X2,X1)!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_33, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_34, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_16]), c_0_25]), c_0_26]), c_0_27])])).
% 0.13/0.39  cnf(c_0_36, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  fof(c_0_40, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_42, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_43, plain, (X1=k6_relat_1(X2)|k5_relat_1(X1,X3)!=X3|k1_relat_1(X1)!=X2|k1_relat_1(X3)!=X2|~v2_funct_1(X3)|~v1_funct_1(X1)|~v1_funct_1(X3)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (k5_relat_1(esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_16]), c_0_25]), c_0_26]), c_0_27])])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_25]), c_0_27])])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (k1_relat_1(esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_38]), c_0_16]), c_0_26])])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_16])).
% 0.13/0.39  cnf(c_0_50, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (k6_relat_1(X1)=esk3_0|esk1_0!=X1|~v5_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_27]), c_0_26]), c_0_48]), c_0_49])])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_50, c_0_25])).
% 0.13/0.39  cnf(c_0_54, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.13/0.39  cnf(c_0_56, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_25])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 58
% 0.13/0.39  # Proof object clause steps            : 35
% 0.13/0.39  # Proof object formula steps           : 23
% 0.13/0.39  # Proof object conjectures             : 24
% 0.13/0.39  # Proof object clause conjectures      : 21
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 20
% 0.13/0.39  # Proof object initial formulas used   : 11
% 0.13/0.39  # Proof object generating inferences   : 13
% 0.13/0.39  # Proof object simplifying inferences  : 32
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 11
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 23
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 22
% 0.13/0.39  # Processed clauses                    : 43
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 43
% 0.13/0.39  # Other redundant clauses eliminated   : 1
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 3
% 0.13/0.39  # Generated clauses                    : 35
% 0.13/0.39  # ...of the previous two non-trivial   : 30
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 34
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 1
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 39
% 0.13/0.39  #    Positive orientable unit clauses  : 18
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 2
% 0.13/0.39  #    Non-unit-clauses                  : 19
% 0.13/0.39  # Current number of unprocessed clauses: 7
% 0.13/0.39  # ...number of literals in the above   : 34
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 4
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 170
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 38
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 21
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 7
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 2704
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.033 s
% 0.13/0.39  # System time              : 0.009 s
% 0.13/0.39  # Total time               : 0.043 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
