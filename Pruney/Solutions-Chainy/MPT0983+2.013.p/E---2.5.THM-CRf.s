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
% DateTime   : Thu Dec  3 11:02:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 767 expanded)
%              Number of clauses        :   55 ( 278 expanded)
%              Number of leaves         :   19 ( 189 expanded)
%              Depth                    :   11
%              Number of atoms          :  316 (4130 expanded)
%              Number of equality atoms :   47 ( 223 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t24_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))
           => k2_relset_1(X1,X2,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t26_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | v2_funct_1(X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
             => ( v2_funct_1(X3)
                & v2_funct_2(X4,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))
    & ( ~ v2_funct_1(esk4_0)
      | ~ v2_funct_2(esk5_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X38,X39] :
      ( ( ~ v2_funct_2(X39,X38)
        | k2_relat_1(X39) = X38
        | ~ v1_relat_1(X39)
        | ~ v5_relat_1(X39,X38) )
      & ( k2_relat_1(X39) != X38
        | v2_funct_2(X39,X38)
        | ~ v1_relat_1(X39)
        | ~ v5_relat_1(X39,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | v1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X48,X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,X49,X48)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48)))
      | ~ r2_relset_1(X49,X49,k1_partfun1(X49,X48,X48,X49,X51,X50),k6_partfun1(X49))
      | k2_relset_1(X48,X49,X50) = X49 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

fof(c_0_24,plain,(
    ! [X47] : k6_partfun1(X47) = k6_relat_1(X47) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X46] :
      ( v1_partfun1(k6_partfun1(X46),X46)
      & m1_subset_1(k6_partfun1(X46),k1_zfmisc_1(k2_zfmisc_1(X46,X46))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_funct_1(esk4_0)
    | ~ v2_funct_2(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_31,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_34,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ r2_relset_1(X34,X35,X36,X37)
        | X36 = X37
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != X37
        | r2_relset_1(X34,X35,X36,X37)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk5_0) != esk2_0
    | ~ v2_funct_1(esk4_0)
    | ~ v5_relat_1(esk5_0,esk2_0)
    | ~ v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_relset_1(X31,X32,X33) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_40,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_47,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | ~ r1_tarski(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_48,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_49,plain,(
    ! [X18] :
      ( ( v1_relat_1(X18)
        | ~ v1_xboole_0(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(X18)
        | ~ v1_xboole_0(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v2_funct_1(X18)
        | ~ v1_xboole_0(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_1])])])).

fof(c_0_50,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | v1_funct_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_51,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_xboole_0(X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_xboole_0(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_52,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_53,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_32])).

fof(c_0_54,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ( v1_funct_1(k1_partfun1(X40,X41,X42,X43,X44,X45))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( m1_subset_1(k1_partfun1(X40,X41,X42,X43,X44,X45),k1_zfmisc_1(k2_zfmisc_1(X40,X43)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk5_0) != esk2_0
    | ~ v2_funct_1(esk4_0)
    | ~ v5_relat_1(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_56,negated_conjecture,
    ( v5_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_57,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_29]),c_0_45]),c_0_46])])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_61,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_62,plain,
    ( v2_funct_1(X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_65,plain,(
    ! [X52,X53,X54,X55,X56] :
      ( ( X54 = k1_xboole_0
        | v2_funct_1(X55)
        | ~ v2_funct_1(k1_partfun1(X52,X53,X53,X54,X55,X56))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X53,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X53 != k1_xboole_0
        | v2_funct_1(X55)
        | ~ v2_funct_1(k1_partfun1(X52,X53,X53,X54,X55,X56))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X53,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_66,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_53])])).

cnf(c_0_67,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_68,plain,(
    ! [X19] :
      ( v1_relat_1(k6_relat_1(X19))
      & v2_funct_1(k6_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk5_0) != esk2_0
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_70,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_29])])).

cnf(c_0_71,plain,
    ( ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_44])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_29]),c_0_44]),c_0_46]),c_0_45])])).

cnf(c_0_78,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

fof(c_0_80,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_81,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v5_relat_1(X1,esk1_1(k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_83,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_43]),c_0_42]),c_0_29]),c_0_44]),c_0_78]),c_0_46]),c_0_45])]),c_0_79])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v5_relat_1(esk5_0,esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_70]),c_0_37])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_79])).

cnf(c_0_88,plain,
    ( v5_relat_1(X1,X2)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( ~ v5_relat_1(esk5_0,esk1_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_83]),c_0_83]),c_0_87])).

cnf(c_0_91,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_83])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.038 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t29_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 0.20/0.39  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.20/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.39  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 0.20/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.39  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.39  fof(cc2_funct_1, axiom, ![X1]:(((v1_xboole_0(X1)&v1_relat_1(X1))&v1_funct_1(X1))=>((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 0.20/0.39  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.20/0.39  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.20/0.39  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 0.20/0.39  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.39  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1)))))), inference(assume_negation,[status(cth)],[t29_funct_2])).
% 0.20/0.39  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))&(~v2_funct_1(esk4_0)|~v2_funct_2(esk5_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.39  fof(c_0_21, plain, ![X38, X39]:((~v2_funct_2(X39,X38)|k2_relat_1(X39)=X38|(~v1_relat_1(X39)|~v5_relat_1(X39,X38)))&(k2_relat_1(X39)!=X38|v2_funct_2(X39,X38)|(~v1_relat_1(X39)|~v5_relat_1(X39,X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.20/0.39  fof(c_0_22, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|v1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.39  fof(c_0_23, plain, ![X48, X49, X50, X51]:(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48)))|(~r2_relset_1(X49,X49,k1_partfun1(X49,X48,X48,X49,X51,X50),k6_partfun1(X49))|k2_relset_1(X48,X49,X50)=X49))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.20/0.39  fof(c_0_24, plain, ![X47]:k6_partfun1(X47)=k6_relat_1(X47), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.39  fof(c_0_25, plain, ![X46]:(v1_partfun1(k6_partfun1(X46),X46)&m1_subset_1(k6_partfun1(X46),k1_zfmisc_1(k2_zfmisc_1(X46,X46)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (~v2_funct_1(esk4_0)|~v2_funct_2(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_27, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_30, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.39  cnf(c_0_31, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_32, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_34, plain, ![X34, X35, X36, X37]:((~r2_relset_1(X34,X35,X36,X37)|X36=X37|(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(X36!=X37|r2_relset_1(X34,X35,X36,X37)|(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.39  cnf(c_0_35, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (k2_relat_1(esk5_0)!=esk2_0|~v2_funct_1(esk4_0)|~v5_relat_1(esk5_0,esk2_0)|~v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.39  cnf(c_0_38, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  fof(c_0_39, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k2_relset_1(X31,X32,X33)=k2_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.39  cnf(c_0_40, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_47, plain, ![X20, X21]:(~r2_hidden(X20,X21)|~r1_tarski(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.39  fof(c_0_48, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.39  fof(c_0_49, plain, ![X18]:(((v1_relat_1(X18)|(~v1_xboole_0(X18)|~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(X18)|(~v1_xboole_0(X18)|~v1_relat_1(X18)|~v1_funct_1(X18))))&(v2_funct_1(X18)|(~v1_xboole_0(X18)|~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_1])])])).
% 0.20/0.39  fof(c_0_50, plain, ![X17]:(~v1_xboole_0(X17)|v1_funct_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.20/0.39  fof(c_0_51, plain, ![X28, X29, X30]:(~v1_xboole_0(X28)|(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_xboole_0(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.20/0.39  cnf(c_0_52, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  cnf(c_0_53, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_35, c_0_32])).
% 0.20/0.39  fof(c_0_54, plain, ![X40, X41, X42, X43, X44, X45]:((v1_funct_1(k1_partfun1(X40,X41,X42,X43,X44,X45))|(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&(m1_subset_1(k1_partfun1(X40,X41,X42,X43,X44,X45),k1_zfmisc_1(k2_zfmisc_1(X40,X43)))|(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (k2_relat_1(esk5_0)!=esk2_0|~v2_funct_1(esk4_0)|~v5_relat_1(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (v5_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 0.20/0.39  cnf(c_0_57, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_29]), c_0_45]), c_0_46])])).
% 0.20/0.39  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  cnf(c_0_60, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  fof(c_0_61, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  cnf(c_0_62, plain, (v2_funct_1(X1)|~v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  cnf(c_0_63, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_64, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.39  fof(c_0_65, plain, ![X52, X53, X54, X55, X56]:((X54=k1_xboole_0|v2_funct_1(X55)|~v2_funct_1(k1_partfun1(X52,X53,X53,X54,X55,X56))|(~v1_funct_1(X56)|~v1_funct_2(X56,X53,X54)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&(X53!=k1_xboole_0|v2_funct_1(X55)|~v2_funct_1(k1_partfun1(X52,X53,X53,X54,X55,X56))|(~v1_funct_1(X56)|~v1_funct_2(X56,X53,X54)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_53])])).
% 0.20/0.39  cnf(c_0_67, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.39  fof(c_0_68, plain, ![X19]:(v1_relat_1(k6_relat_1(X19))&v2_funct_1(k6_relat_1(X19))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk5_0)!=esk2_0|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_29])])).
% 0.20/0.39  cnf(c_0_71, plain, (~v5_relat_1(X1,X2)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.39  cnf(c_0_72, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.39  cnf(c_0_73, plain, (v2_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(X1)), inference(csr,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_44])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_44])).
% 0.20/0.39  cnf(c_0_76, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_29]), c_0_44]), c_0_46]), c_0_45])])).
% 0.20/0.39  cnf(c_0_78, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.20/0.39  fof(c_0_80, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_81, plain, (v1_xboole_0(k2_relat_1(X1))|~v5_relat_1(X1,esk1_1(k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (v2_funct_1(esk4_0)|~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_43]), c_0_42]), c_0_29]), c_0_44]), c_0_78]), c_0_46]), c_0_45])]), c_0_79])).
% 0.20/0.39  cnf(c_0_84, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.39  cnf(c_0_85, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (v1_xboole_0(esk2_0)|~v5_relat_1(esk5_0,esk1_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_70]), c_0_37])])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_79])).
% 0.20/0.39  cnf(c_0_88, plain, (v5_relat_1(X1,X2)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_38, c_0_84])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_85])).
% 0.20/0.39  cnf(c_0_90, negated_conjecture, (~v5_relat_1(esk5_0,esk1_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_83]), c_0_83]), c_0_87])).
% 0.20/0.39  cnf(c_0_91, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_88])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_83])])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 94
% 0.20/0.39  # Proof object clause steps            : 55
% 0.20/0.39  # Proof object formula steps           : 39
% 0.20/0.39  # Proof object conjectures             : 32
% 0.20/0.39  # Proof object clause conjectures      : 29
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 27
% 0.20/0.39  # Proof object initial formulas used   : 19
% 0.20/0.39  # Proof object generating inferences   : 18
% 0.20/0.39  # Proof object simplifying inferences  : 48
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 21
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 42
% 0.20/0.39  # Removed in clause preprocessing      : 3
% 0.20/0.40  # Initial clauses in saturation        : 39
% 0.20/0.40  # Processed clauses                    : 121
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 12
% 0.20/0.40  # ...remaining for further processing  : 108
% 0.20/0.40  # Other redundant clauses eliminated   : 1
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 5
% 0.20/0.40  # Backward-rewritten                   : 21
% 0.20/0.40  # Generated clauses                    : 125
% 0.20/0.40  # ...of the previous two non-trivial   : 111
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 121
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 4
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 81
% 0.20/0.40  #    Positive orientable unit clauses  : 34
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 42
% 0.20/0.40  # Current number of unprocessed clauses: 22
% 0.20/0.40  # ...number of literals in the above   : 90
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 27
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 638
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 160
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.40  # Unit Clause-clause subsumption calls : 82
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 7
% 0.20/0.40  # BW rewrite match successes           : 7
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 4674
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.042 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.049 s
% 0.20/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
