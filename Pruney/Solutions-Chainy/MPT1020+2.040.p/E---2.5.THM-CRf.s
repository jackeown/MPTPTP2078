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
% DateTime   : Thu Dec  3 11:06:03 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 (1524 expanded)
%              Number of clauses        :   57 ( 576 expanded)
%              Number of leaves         :   16 ( 372 expanded)
%              Depth                    :   11
%              Number of atoms          :  309 (9196 expanded)
%              Number of equality atoms :   79 ( 620 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   16 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t197_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( k2_relat_1(X1) = k1_xboole_0
              & k2_relat_1(X2) = k1_xboole_0 )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t67_funct_1,axiom,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ v1_funct_1(X40)
      | ~ v1_funct_2(X40,X38,X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,X39,X38)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
      | k2_relset_1(X38,X39,X40) != X39
      | ~ r2_relset_1(X38,X38,k1_partfun1(X38,X39,X39,X38,X40,X41),k6_partfun1(X38))
      | ~ v2_funct_1(X40)
      | X38 = k1_xboole_0
      | X39 = k1_xboole_0
      | X41 = k2_funct_1(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).

fof(c_0_18,plain,(
    ! [X29] : k6_partfun1(X29) = k6_relat_1(X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_19,plain,(
    ! [X34,X35,X36,X37] :
      ( ( v2_funct_1(X36)
        | ~ r2_relset_1(X34,X34,k1_partfun1(X34,X35,X35,X34,X36,X37),k6_partfun1(X34))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v2_funct_2(X37,X34)
        | ~ r2_relset_1(X34,X34,k1_partfun1(X34,X35,X35,X34,X36,X37),k6_partfun1(X34))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] :
      ( ( v4_relat_1(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( v5_relat_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_21,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ( v1_funct_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v3_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v2_funct_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v3_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v2_funct_2(X24,X23)
        | ~ v1_funct_1(X24)
        | ~ v3_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v2_funct_1(X1)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X25,X26] :
      ( ( ~ v2_funct_2(X26,X25)
        | k2_relat_1(X26) = X25
        | ~ v1_relat_1(X26)
        | ~ v5_relat_1(X26,X25) )
      & ( k2_relat_1(X26) != X25
        | v2_funct_2(X26,X25)
        | ~ v1_relat_1(X26)
        | ~ v5_relat_1(X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_28,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_34,plain,(
    ! [X7] :
      ( v1_relat_1(k6_relat_1(X7))
      & v2_funct_1(k6_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_35,plain,(
    ! [X27,X28] :
      ( ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,X27,X27)
      | ~ v3_funct_2(X28,X27,X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X27)))
      | k2_funct_2(X27,X28) = k2_funct_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

cnf(c_0_36,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X4 = k2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

fof(c_0_38,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k2_relset_1(X15,X16,X17) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_39,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v2_funct_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_29])])).

fof(c_0_43,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ r2_relset_1(X18,X19,X20,X21)
        | X20 = X21
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X20 != X21
        | r2_relset_1(X18,X19,X20,X21)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_44,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k2_relat_1(X5) != k1_xboole_0
      | k2_relat_1(X6) != k1_xboole_0
      | X5 = X6 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t197_relat_1])])])).

cnf(c_0_45,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( v3_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,plain,
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
    inference(csr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_53,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),c_0_42])])).

cnf(c_0_55,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_relat_1(X1) != k1_xboole_0
    | k2_relat_1(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_59,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( v2_funct_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_48]),c_0_49]),c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_64,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = k2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_51]),c_0_33]),c_0_29])])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k2_funct_1(esk2_0)
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,esk2_0) != X3
    | ~ v1_funct_2(esk2_0,X2,X3)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,esk2_0,X1),k6_relat_1(X2))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_25])).

cnf(c_0_69,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( k1_xboole_0 = X1
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_71,negated_conjecture,
    ( esk2_0 = X1
    | k2_relat_1(X1) != k1_xboole_0
    | esk1_0 != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_41])])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_60]),c_0_61])]),c_0_62])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( k2_funct_1(esk2_0) = esk3_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_47]),c_0_66]),c_0_51]),c_0_67]),c_0_49]),c_0_68]),c_0_29])])).

cnf(c_0_75,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_47])).

cnf(c_0_76,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k2_relat_1(esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_41])).

fof(c_0_77,plain,(
    ! [X8] : k2_funct_1(k6_relat_1(X8)) = k6_relat_1(X8) ),
    inference(variable_rename,[status(thm)],[t67_funct_1])).

cnf(c_0_78,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk1_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_61]),c_0_72])])).

cnf(c_0_79,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_76,c_0_54])).

cnf(c_0_81,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_79])])).

cnf(c_0_84,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_46])).

cnf(c_0_85,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_79]),c_0_79]),c_0_82]),c_0_83]),c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_79]),c_0_79]),c_0_83]),c_0_83]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EI
% 0.21/0.39  # and selection function SelectDivPreferIntoLits.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.033 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t87_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 0.21/0.39  fof(t36_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 0.21/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.21/0.39  fof(t29_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 0.21/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.39  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.21/0.39  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.21/0.39  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.21/0.39  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.21/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.21/0.39  fof(t197_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((k2_relat_1(X1)=k1_xboole_0&k2_relat_1(X2)=k1_xboole_0)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t197_relat_1)).
% 0.21/0.39  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.21/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.39  fof(t67_funct_1, axiom, ![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 0.21/0.39  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)))))), inference(assume_negation,[status(cth)],[t87_funct_2])).
% 0.21/0.39  fof(c_0_17, plain, ![X38, X39, X40, X41]:(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X38)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))|(k2_relset_1(X38,X39,X40)!=X39|~r2_relset_1(X38,X38,k1_partfun1(X38,X39,X39,X38,X40,X41),k6_partfun1(X38))|~v2_funct_1(X40)|(X38=k1_xboole_0|X39=k1_xboole_0|X41=k2_funct_1(X40))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).
% 0.21/0.39  fof(c_0_18, plain, ![X29]:k6_partfun1(X29)=k6_relat_1(X29), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.21/0.39  fof(c_0_19, plain, ![X34, X35, X36, X37]:((v2_funct_1(X36)|~r2_relset_1(X34,X34,k1_partfun1(X34,X35,X35,X34,X36,X37),k6_partfun1(X34))|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X34)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X34))))|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(v2_funct_2(X37,X34)|~r2_relset_1(X34,X34,k1_partfun1(X34,X35,X35,X34,X36,X37),k6_partfun1(X34))|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X34)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X34))))|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).
% 0.21/0.39  fof(c_0_20, plain, ![X12, X13, X14]:((v4_relat_1(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))&(v5_relat_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.39  fof(c_0_21, negated_conjecture, ((((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&v3_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&v3_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0))&~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.21/0.39  fof(c_0_22, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.39  fof(c_0_23, plain, ![X22, X23, X24]:(((v1_funct_1(X24)|(~v1_funct_1(X24)|~v3_funct_2(X24,X22,X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(v2_funct_1(X24)|(~v1_funct_1(X24)|~v3_funct_2(X24,X22,X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&(v2_funct_2(X24,X23)|(~v1_funct_1(X24)|~v3_funct_2(X24,X22,X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.21/0.39  cnf(c_0_24, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X4=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|k2_relset_1(X2,X3,X1)!=X3|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_25, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_26, plain, (v2_funct_1(X1)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  fof(c_0_27, plain, ![X25, X26]:((~v2_funct_2(X26,X25)|k2_relat_1(X26)=X25|(~v1_relat_1(X26)|~v5_relat_1(X26,X25)))&(k2_relat_1(X26)!=X25|v2_funct_2(X26,X25)|(~v1_relat_1(X26)|~v5_relat_1(X26,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.21/0.39  cnf(c_0_28, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_31, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (v3_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  fof(c_0_34, plain, ![X7]:(v1_relat_1(k6_relat_1(X7))&v2_funct_1(k6_relat_1(X7))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.21/0.39  fof(c_0_35, plain, ![X27, X28]:(~v1_funct_1(X28)|~v1_funct_2(X28,X27,X27)|~v3_funct_2(X28,X27,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X27)))|k2_funct_2(X27,X28)=k2_funct_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.21/0.39  cnf(c_0_36, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.39  cnf(c_0_37, plain, (v2_funct_1(X1)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.21/0.39  fof(c_0_38, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k2_relset_1(X15,X16,X17)=k2_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.39  cnf(c_0_39, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (v5_relat_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (v2_funct_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_29])])).
% 0.21/0.39  fof(c_0_43, plain, ![X18, X19, X20, X21]:((~r2_relset_1(X18,X19,X20,X21)|X20=X21|(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&(X20!=X21|r2_relset_1(X18,X19,X20,X21)|(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.21/0.39  fof(c_0_44, plain, ![X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|(k2_relat_1(X5)!=k1_xboole_0|k2_relat_1(X6)!=k1_xboole_0|X5=X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t197_relat_1])])])).
% 0.21/0.39  cnf(c_0_45, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.39  cnf(c_0_46, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (v3_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_50, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_52, plain, (X1=k2_funct_1(X2)|X3=k1_xboole_0|X4=k1_xboole_0|k2_relset_1(X3,X4,X2)!=X4|~v1_funct_2(X1,X4,X3)|~v1_funct_2(X2,X3,X4)|~v1_funct_1(X1)|~v1_funct_1(X2)|~r2_relset_1(X3,X3,k1_partfun1(X3,X4,X4,X3,X2,X1),k6_relat_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(csr,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.39  cnf(c_0_53, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (k2_relat_1(esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), c_0_42])])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_56, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.39  cnf(c_0_57, plain, (X1=X2|~v1_relat_1(X1)|~v1_relat_1(X2)|k2_relat_1(X1)!=k1_xboole_0|k2_relat_1(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.39  cnf(c_0_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.39  cnf(c_0_59, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_47])).
% 0.21/0.39  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_47])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (v2_funct_2(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_48]), c_0_49]), c_0_47])])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=k2_funct_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_51]), c_0_33]), c_0_29])])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (X1=k2_funct_1(esk2_0)|X2=k1_xboole_0|X3=k1_xboole_0|k2_relset_1(X2,X3,esk2_0)!=X3|~v1_funct_2(esk2_0,X2,X3)|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,esk2_0,X1),k6_relat_1(X2))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_33])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_54])).
% 0.21/0.39  cnf(c_0_67, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_55, c_0_25])).
% 0.21/0.39  cnf(c_0_69, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_56])).
% 0.21/0.39  cnf(c_0_70, plain, (k1_xboole_0=X1|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.21/0.39  cnf(c_0_71, negated_conjecture, (esk2_0=X1|k2_relat_1(X1)!=k1_xboole_0|esk1_0!=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_54]), c_0_41])])).
% 0.21/0.39  cnf(c_0_72, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_60]), c_0_61])]), c_0_62])])).
% 0.21/0.39  cnf(c_0_73, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk2_0))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (k2_funct_1(esk2_0)=esk3_0|esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_47]), c_0_66]), c_0_51]), c_0_67]), c_0_49]), c_0_68]), c_0_29])])).
% 0.21/0.39  cnf(c_0_75, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_47])).
% 0.21/0.39  cnf(c_0_76, negated_conjecture, (esk2_0=k1_xboole_0|k2_relat_1(esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_41])).
% 0.21/0.39  fof(c_0_77, plain, ![X8]:k2_funct_1(k6_relat_1(X8))=k6_relat_1(X8), inference(variable_rename,[status(thm)],[t67_funct_1])).
% 0.21/0.39  cnf(c_0_78, negated_conjecture, (esk3_0=esk2_0|esk1_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_61]), c_0_72])])).
% 0.21/0.39  cnf(c_0_79, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.21/0.39  cnf(c_0_80, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_76, c_0_54])).
% 0.21/0.39  cnf(c_0_81, plain, (k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_79])])).
% 0.21/0.39  cnf(c_0_84, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_46])).
% 0.21/0.39  cnf(c_0_85, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_69, c_0_29])).
% 0.21/0.39  cnf(c_0_86, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_79]), c_0_79]), c_0_82]), c_0_83]), c_0_83]), c_0_84])).
% 0.21/0.39  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_79]), c_0_79]), c_0_83]), c_0_83]), c_0_86]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 88
% 0.21/0.39  # Proof object clause steps            : 57
% 0.21/0.39  # Proof object formula steps           : 31
% 0.21/0.39  # Proof object conjectures             : 38
% 0.21/0.39  # Proof object clause conjectures      : 35
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 25
% 0.21/0.39  # Proof object initial formulas used   : 16
% 0.21/0.39  # Proof object generating inferences   : 21
% 0.21/0.39  # Proof object simplifying inferences  : 56
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 17
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 34
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 32
% 0.21/0.39  # Processed clauses                    : 144
% 0.21/0.39  # ...of these trivial                  : 13
% 0.21/0.39  # ...subsumed                          : 6
% 0.21/0.39  # ...remaining for further processing  : 124
% 0.21/0.39  # Other redundant clauses eliminated   : 2
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 50
% 0.21/0.39  # Generated clauses                    : 68
% 0.21/0.39  # ...of the previous two non-trivial   : 99
% 0.21/0.39  # Contextual simplify-reflections      : 1
% 0.21/0.39  # Paramodulations                      : 66
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 2
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
% 0.21/0.39  # Current number of processed clauses  : 40
% 0.21/0.39  #    Positive orientable unit clauses  : 19
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 20
% 0.21/0.39  # Current number of unprocessed clauses: 18
% 0.21/0.39  # ...number of literals in the above   : 90
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 83
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1208
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 155
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 7
% 0.21/0.39  # Unit Clause-clause subsumption calls : 6
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 15
% 0.21/0.39  # BW rewrite match successes           : 7
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 4973
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.044 s
% 0.21/0.39  # System time              : 0.007 s
% 0.21/0.39  # Total time               : 0.051 s
% 0.21/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
