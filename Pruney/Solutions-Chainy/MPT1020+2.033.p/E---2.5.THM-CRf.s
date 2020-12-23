%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:02 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 741 expanded)
%              Number of clauses        :   65 ( 296 expanded)
%              Number of leaves         :   15 ( 174 expanded)
%              Depth                    :   12
%              Number of atoms          :  337 (4270 expanded)
%              Number of equality atoms :   81 ( 323 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & v3_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))
           => r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(t29_funct_2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t36_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
              & v2_funct_1(X3) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t67_funct_1,axiom,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & v3_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))
             => r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t87_funct_2])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & v3_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & v3_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0))
    & ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( ~ v2_funct_2(X27,X26)
        | k2_relat_1(X27) = X26
        | ~ v1_relat_1(X27)
        | ~ v5_relat_1(X27,X26) )
      & ( k2_relat_1(X27) != X26
        | v2_funct_2(X27,X26)
        | ~ v1_relat_1(X27)
        | ~ v5_relat_1(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] :
      ( ( v4_relat_1(X15,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v5_relat_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] :
      ( ( v1_funct_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v3_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v2_funct_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v3_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v2_funct_2(X25,X24)
        | ~ v1_funct_1(X25)
        | ~ v3_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_23,plain,(
    ! [X32,X33,X34,X35] :
      ( ( v2_funct_1(X34)
        | ~ r2_relset_1(X32,X32,k1_partfun1(X32,X33,X33,X32,X34,X35),k6_partfun1(X32))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X32)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X32)))
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v2_funct_2(X35,X32)
        | ~ r2_relset_1(X32,X32,k1_partfun1(X32,X33,X33,X32,X34,X35),k6_partfun1(X32))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X32)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X32)))
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).

fof(c_0_24,plain,(
    ! [X31] : k6_partfun1(X31) = k6_relat_1(X31) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,X36,X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,X37,X36)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X36)))
      | k2_relset_1(X36,X37,X38) != X37
      | ~ r2_relset_1(X36,X36,k1_partfun1(X36,X37,X37,X36,X38,X39),k6_partfun1(X36))
      | ~ v2_funct_1(X38)
      | X36 = k1_xboole_0
      | X37 = k1_xboole_0
      | X39 = k2_funct_1(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).

cnf(c_0_26,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( v2_funct_2(X1,X2)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_partfun1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X29,X30] :
      ( ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,X29,X29)
      | ~ v3_funct_2(X30,X29,X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29)))
      | k2_funct_2(X29,X30) = k2_funct_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

cnf(c_0_34,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v2_funct_1(X1)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k2_relset_1(X16,X17,X18) = k2_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(esk2_0) = X1
    | ~ v2_funct_2(esk2_0,X1)
    | ~ v5_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( v2_funct_2(esk2_0,X1)
    | ~ v3_funct_2(esk2_0,X2,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_41,plain,(
    ! [X28] :
      ( v1_partfun1(k6_partfun1(X28),X28)
      & m1_subset_1(k6_partfun1(X28),k1_zfmisc_1(k2_zfmisc_1(X28,X28))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X4 = k2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_49,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_50,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0
    | ~ v2_funct_2(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( v2_funct_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_40])])).

fof(c_0_53,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_relset_1(X19,X20,X21,X22)
        | X21 = X22
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != X22
        | r2_relset_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_55,plain,(
    ! [X7] :
      ( ( k1_relat_1(X7) != k1_xboole_0
        | X7 = k1_xboole_0
        | ~ v1_relat_1(X7) )
      & ( k2_relat_1(X7) != k1_xboole_0
        | X7 = k1_xboole_0
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( v2_funct_2(esk3_0,esk1_0)
    | ~ v1_funct_2(X1,esk1_0,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,X1,esk3_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_42])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( k2_funct_2(X1,esk2_0) = k2_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,X1,X1)
    | ~ v3_funct_2(esk2_0,X1,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_30])).

cnf(c_0_61,plain,
    ( X1 = k2_funct_1(X2)
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_relset_1(X3,X4,X2) != X4
    | ~ v1_funct_2(X1,X4,X3)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X4,X4,X3,X2,X1),k6_relat_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(csr,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = k2_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_64,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_32])).

fof(c_0_66,plain,(
    ! [X8] :
      ( k1_relat_1(k6_relat_1(X8)) = X8
      & k2_relat_1(k6_relat_1(X8)) = X8 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( k2_relat_1(esk3_0) = X1
    | ~ v2_funct_2(esk3_0,X1)
    | ~ v5_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( v2_funct_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_58]),c_0_59]),c_0_20])])).

cnf(c_0_70,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = k2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_20]),c_0_58]),c_0_40])])).

cnf(c_0_73,negated_conjecture,
    ( k2_funct_1(X1) = esk3_0
    | esk1_0 = k1_xboole_0
    | k2_relset_1(esk1_0,esk1_0,X1) != esk1_0
    | ~ v1_funct_2(X1,esk1_0,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,X1,esk3_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_44]),c_0_45]),c_0_42])])).

cnf(c_0_74,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_65])).

cnf(c_0_77,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k2_relat_1(esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k2_funct_1(esk2_0) = esk3_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_58]),c_0_74]),c_0_30]),c_0_59]),c_0_20])])).

cnf(c_0_82,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_42])).

cnf(c_0_83,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k2_relat_1(esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_27])).

fof(c_0_84,plain,(
    ! [X9] : k2_funct_1(k6_relat_1(X9)) = k6_relat_1(X9) ),
    inference(variable_rename,[status(thm)],[t67_funct_1])).

cnf(c_0_85,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_76]),c_0_77])])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

cnf(c_0_88,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_83,c_0_63])).

cnf(c_0_89,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_92,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_87])])).

cnf(c_0_93,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_85])).

cnf(c_0_94,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_87]),c_0_87]),c_0_91]),c_0_92]),c_0_93]),c_0_94])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:37:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EI
% 0.21/0.39  # and selection function SelectDivPreferIntoLits.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t87_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 0.21/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.39  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.21/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.39  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.21/0.39  fof(t29_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 0.21/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.21/0.39  fof(t36_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.21/0.39  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.21/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.39  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.21/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.21/0.39  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.21/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.39  fof(t67_funct_1, axiom, ![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 0.21/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)))))), inference(assume_negation,[status(cth)],[t87_funct_2])).
% 0.21/0.39  fof(c_0_16, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.39  fof(c_0_17, negated_conjecture, ((((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&v3_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&v3_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0))&~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.21/0.39  fof(c_0_18, plain, ![X26, X27]:((~v2_funct_2(X27,X26)|k2_relat_1(X27)=X26|(~v1_relat_1(X27)|~v5_relat_1(X27,X26)))&(k2_relat_1(X27)!=X26|v2_funct_2(X27,X26)|(~v1_relat_1(X27)|~v5_relat_1(X27,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.21/0.39  cnf(c_0_19, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  fof(c_0_21, plain, ![X13, X14, X15]:((v4_relat_1(X15,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))&(v5_relat_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.39  fof(c_0_22, plain, ![X23, X24, X25]:(((v1_funct_1(X25)|(~v1_funct_1(X25)|~v3_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v2_funct_1(X25)|(~v1_funct_1(X25)|~v3_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(v2_funct_2(X25,X24)|(~v1_funct_1(X25)|~v3_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.21/0.39  fof(c_0_23, plain, ![X32, X33, X34, X35]:((v2_funct_1(X34)|~r2_relset_1(X32,X32,k1_partfun1(X32,X33,X33,X32,X34,X35),k6_partfun1(X32))|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X32)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X32))))|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(v2_funct_2(X35,X32)|~r2_relset_1(X32,X32,k1_partfun1(X32,X33,X33,X32,X34,X35),k6_partfun1(X32))|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X32)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X32))))|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).
% 0.21/0.39  fof(c_0_24, plain, ![X31]:k6_partfun1(X31)=k6_relat_1(X31), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.21/0.39  fof(c_0_25, plain, ![X36, X37, X38, X39]:(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|(~v1_funct_1(X39)|~v1_funct_2(X39,X37,X36)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X36)))|(k2_relset_1(X36,X37,X38)!=X37|~r2_relset_1(X36,X36,k1_partfun1(X36,X37,X37,X36,X38,X39),k6_partfun1(X36))|~v2_funct_1(X38)|(X36=k1_xboole_0|X37=k1_xboole_0|X39=k2_funct_1(X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).
% 0.21/0.39  cnf(c_0_26, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.39  cnf(c_0_28, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_29, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_31, plain, (v2_funct_2(X1,X2)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_partfun1(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_32, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  fof(c_0_33, plain, ![X29, X30]:(~v1_funct_1(X30)|~v1_funct_2(X30,X29,X29)|~v3_funct_2(X30,X29,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29)))|k2_funct_2(X29,X30)=k2_funct_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.21/0.39  cnf(c_0_34, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X4=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|k2_relset_1(X2,X3,X1)!=X3|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_35, plain, (v2_funct_1(X1)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  fof(c_0_36, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k2_relset_1(X16,X17,X18)=k2_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (k2_relat_1(esk2_0)=X1|~v2_funct_2(esk2_0,X1)|~v5_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (v5_relat_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (v2_funct_2(esk2_0,X1)|~v3_funct_2(esk2_0,X2,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (v3_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  fof(c_0_41, plain, ![X28]:(v1_partfun1(k6_partfun1(X28),X28)&m1_subset_1(k6_partfun1(X28),k1_zfmisc_1(k2_zfmisc_1(X28,X28)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_43, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X2,X3)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_47, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_48, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_34, c_0_32])).
% 0.21/0.39  cnf(c_0_49, plain, (v2_funct_1(X1)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_35, c_0_32])).
% 0.21/0.39  cnf(c_0_50, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (k2_relat_1(esk2_0)=esk1_0|~v2_funct_2(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (v2_funct_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_40])])).
% 0.21/0.39  fof(c_0_53, plain, ![X19, X20, X21, X22]:((~r2_relset_1(X19,X20,X21,X22)|X21=X22|(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&(X21!=X22|r2_relset_1(X19,X20,X21,X22)|(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.21/0.39  cnf(c_0_54, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.39  fof(c_0_55, plain, ![X7]:((k1_relat_1(X7)!=k1_xboole_0|X7=k1_xboole_0|~v1_relat_1(X7))&(k2_relat_1(X7)!=k1_xboole_0|X7=k1_xboole_0|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_42])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (v2_funct_2(esk3_0,esk1_0)|~v1_funct_2(X1,esk1_0,esk1_0)|~v1_funct_1(X1)|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,X1,esk3_0),k6_relat_1(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_42])])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_46, c_0_32])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (k2_funct_2(X1,esk2_0)=k2_funct_1(esk2_0)|~v1_funct_2(esk2_0,X1,X1)|~v3_funct_2(esk2_0,X1,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_30])).
% 0.21/0.39  cnf(c_0_61, plain, (X1=k2_funct_1(X2)|X3=k1_xboole_0|X4=k1_xboole_0|k2_relset_1(X3,X4,X2)!=X4|~v1_funct_2(X1,X4,X3)|~v1_funct_2(X2,X3,X4)|~v1_funct_1(X1)|~v1_funct_1(X2)|~r2_relset_1(X3,X3,k1_partfun1(X3,X4,X4,X3,X2,X1),k6_relat_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(csr,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk2_0)=k2_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_20])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.21/0.39  cnf(c_0_64, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.39  cnf(c_0_65, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_54, c_0_32])).
% 0.21/0.39  fof(c_0_66, plain, ![X8]:(k1_relat_1(k6_relat_1(X8))=X8&k2_relat_1(k6_relat_1(X8))=X8), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.39  cnf(c_0_67, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (k2_relat_1(esk3_0)=X1|~v2_funct_2(esk3_0,X1)|~v5_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_56])).
% 0.21/0.39  cnf(c_0_69, negated_conjecture, (v2_funct_2(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_30]), c_0_58]), c_0_59]), c_0_20])])).
% 0.21/0.39  cnf(c_0_70, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 0.21/0.39  cnf(c_0_71, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_72, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=k2_funct_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_20]), c_0_58]), c_0_40])])).
% 0.21/0.39  cnf(c_0_73, negated_conjecture, (k2_funct_1(X1)=esk3_0|esk1_0=k1_xboole_0|k2_relset_1(esk1_0,esk1_0,X1)!=esk1_0|~v1_funct_2(X1,esk1_0,esk1_0)|~v1_funct_1(X1)|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,X1,esk3_0),k6_relat_1(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_44]), c_0_45]), c_0_42])])).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.39  cnf(c_0_75, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_64])).
% 0.21/0.39  cnf(c_0_76, plain, (v1_relat_1(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_65])).
% 0.21/0.39  cnf(c_0_77, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.39  cnf(c_0_78, negated_conjecture, (esk3_0=k1_xboole_0|k2_relat_1(esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_56])).
% 0.21/0.39  cnf(c_0_79, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.21/0.39  cnf(c_0_80, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk2_0))), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, (k2_funct_1(esk2_0)=esk3_0|esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_58]), c_0_74]), c_0_30]), c_0_59]), c_0_20])])).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_75, c_0_42])).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (esk2_0=k1_xboole_0|k2_relat_1(esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_27])).
% 0.21/0.39  fof(c_0_84, plain, ![X9]:k2_funct_1(k6_relat_1(X9))=k6_relat_1(X9), inference(variable_rename,[status(thm)],[t67_funct_1])).
% 0.21/0.39  cnf(c_0_85, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_76]), c_0_77])])).
% 0.21/0.39  cnf(c_0_86, negated_conjecture, (esk3_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.39  cnf(c_0_87, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])])).
% 0.21/0.39  cnf(c_0_88, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_83, c_0_63])).
% 0.21/0.39  cnf(c_0_89, plain, (k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.21/0.39  cnf(c_0_90, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_65, c_0_85])).
% 0.21/0.39  cnf(c_0_91, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.21/0.39  cnf(c_0_92, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_87])])).
% 0.21/0.39  cnf(c_0_93, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_89, c_0_85])).
% 0.21/0.39  cnf(c_0_94, plain, (r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_75, c_0_90])).
% 0.21/0.39  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_87]), c_0_87]), c_0_91]), c_0_92]), c_0_93]), c_0_94])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 96
% 0.21/0.39  # Proof object clause steps            : 65
% 0.21/0.39  # Proof object formula steps           : 31
% 0.21/0.39  # Proof object conjectures             : 42
% 0.21/0.39  # Proof object clause conjectures      : 39
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 24
% 0.21/0.39  # Proof object initial formulas used   : 15
% 0.21/0.39  # Proof object generating inferences   : 26
% 0.21/0.39  # Proof object simplifying inferences  : 50
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 17
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 35
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 33
% 0.21/0.39  # Processed clauses                    : 162
% 0.21/0.39  # ...of these trivial                  : 16
% 0.21/0.39  # ...subsumed                          : 3
% 0.21/0.39  # ...remaining for further processing  : 142
% 0.21/0.39  # Other redundant clauses eliminated   : 4
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 56
% 0.21/0.39  # Generated clauses                    : 84
% 0.21/0.39  # ...of the previous two non-trivial   : 120
% 0.21/0.39  # Contextual simplify-reflections      : 1
% 0.21/0.39  # Paramodulations                      : 80
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 4
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 51
% 0.21/0.39  #    Positive orientable unit clauses  : 30
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 21
% 0.21/0.39  # Current number of unprocessed clauses: 22
% 0.21/0.39  # ...number of literals in the above   : 53
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 90
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1394
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 211
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 4
% 0.21/0.39  # Unit Clause-clause subsumption calls : 18
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 33
% 0.21/0.39  # BW rewrite match successes           : 9
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 4797
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.038 s
% 0.21/0.39  # System time              : 0.003 s
% 0.21/0.39  # Total time               : 0.041 s
% 0.21/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
