%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 (5296 expanded)
%              Number of clauses        :   92 (1922 expanded)
%              Number of leaves         :   28 (1350 expanded)
%              Depth                    :   20
%              Number of atoms          :  499 (26333 expanded)
%              Number of equality atoms :  151 (1797 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(t44_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = X1 )
           => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

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

fof(t164_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(t66_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X2) )
           => k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(c_0_28,negated_conjecture,(
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

fof(c_0_29,plain,(
    ! [X43,X44,X45,X46] :
      ( ( ~ r2_relset_1(X43,X44,X45,X46)
        | X45 = X46
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X45 != X46
        | r2_relset_1(X43,X44,X45,X46)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_30,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_31,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_34,plain,(
    ! [X50,X51,X52,X53,X54,X55] :
      ( ( v1_funct_1(k1_partfun1(X50,X51,X52,X53,X54,X55))
        | ~ v1_funct_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ v1_funct_1(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( m1_subset_1(k1_partfun1(X50,X51,X52,X53,X54,X55),k1_zfmisc_1(k2_zfmisc_1(X50,X53)))
        | ~ v1_funct_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ v1_funct_1(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_35,plain,(
    ! [X56,X57,X58,X59,X60,X61] :
      ( ~ v1_funct_1(X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | ~ v1_funct_1(X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | k1_partfun1(X56,X57,X58,X59,X60,X61) = k5_relat_1(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_36,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = esk2_0
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_42,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_43,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_44,plain,(
    ! [X71,X72] :
      ( ~ v1_funct_1(X72)
      | ~ v1_funct_2(X72,X71,X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X71,X71)))
      | k1_relset_1(X71,X71,X72) = X71 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_45,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | k2_relat_1(X28) != k1_relat_1(X29)
      | k5_relat_1(X28,X29) != X28
      | X29 = k6_relat_1(k1_relat_1(X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).

cnf(c_0_46,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_33]),c_0_40])])).

cnf(c_0_48,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X62] : k6_partfun1(X62) = k6_relat_1(X62) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_53,plain,
    ( X2 = k6_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k5_relat_1(esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38]),c_0_39]),c_0_33]),c_0_40])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_49])])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_49])])).

cnf(c_0_57,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_59,plain,(
    ! [X20] :
      ( ( k1_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) )
      & ( k2_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_60,plain,(
    ! [X21] :
      ( k1_relat_1(k6_relat_1(X21)) = X21
      & k2_relat_1(k6_relat_1(X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_61,plain,(
    ! [X24] :
      ( v1_relat_1(k6_relat_1(X24))
      & v2_funct_1(k6_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_63,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk2_0)) = esk2_0
    | k1_relat_1(esk2_0) != k2_relat_1(esk3_0)
    | esk3_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_38]),c_0_39]),c_0_55]),c_0_56])])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_38]),c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk2_0
    | k2_relat_1(esk3_0) != esk1_0
    | esk3_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_66]),c_0_39]),c_0_40])])).

cnf(c_0_74,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])])).

fof(c_0_75,plain,(
    ! [X33,X34,X35] :
      ( ( v4_relat_1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v5_relat_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(esk3_0) != esk1_0
    | esk3_0 != esk2_0
    | ~ r2_relset_1(esk1_0,esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_56])])).

cnf(c_0_78,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_65]),c_0_55])])).

fof(c_0_80,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ v4_relat_1(X19,X18)
      | X19 = k7_relat_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_81,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_79])).

cnf(c_0_83,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_84,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k10_relat_1(X17,k2_relat_1(X17)) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_85,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k2_relat_1(k7_relat_1(X14,X13)) = k9_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_86,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( v4_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_33])).

fof(c_0_88,plain,(
    ! [X63,X64,X65,X66,X67] :
      ( ( X65 = k1_xboole_0
        | v2_funct_1(X66)
        | ~ v2_funct_1(k1_partfun1(X63,X64,X64,X65,X66,X67))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X63,X64)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X64 != k1_xboole_0
        | v2_funct_1(X66)
        | ~ v2_funct_1(k1_partfun1(X63,X64,X64,X65,X66,X67))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X63,X64)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_89,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_79])).

cnf(c_0_90,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_83])).

fof(c_0_91,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | ~ r1_tarski(X26,k1_relat_1(X27))
      | ~ v2_funct_1(X27)
      | k10_relat_1(X27,k9_relat_1(X27,X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).

fof(c_0_92,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | k2_relat_1(k5_relat_1(X15,X16)) = k9_relat_1(X16,k2_relat_1(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_93,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_55])])).

fof(c_0_96,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ v2_funct_1(X31)
      | ~ v2_funct_1(X32)
      | k2_funct_1(k5_relat_1(X31,X32)) = k5_relat_1(k2_funct_1(X32),k2_funct_1(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).

fof(c_0_97,plain,(
    ! [X25] :
      ( ( v1_relat_1(k2_funct_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v2_funct_1(X25) )
      & ( v1_funct_1(k2_funct_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v2_funct_1(X25) )
      & ( v2_funct_1(k2_funct_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v2_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_100,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_101,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_102,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_103,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_104,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) = k2_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_55])])).

fof(c_0_105,plain,(
    ! [X68,X69,X70] :
      ( ( k5_relat_1(X70,k2_funct_1(X70)) = k6_partfun1(X68)
        | X69 = k1_xboole_0
        | k2_relset_1(X68,X69,X70) != X69
        | ~ v2_funct_1(X70)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( k5_relat_1(k2_funct_1(X70),X70) = k6_partfun1(X69)
        | X69 = k1_xboole_0
        | k2_relset_1(X68,X69,X70) != X69
        | ~ v2_funct_1(X70)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

cnf(c_0_106,plain,
    ( k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_107,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_108,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_109,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_47]),c_0_58]),c_0_66]),c_0_38]),c_0_39]),c_0_99]),c_0_33]),c_0_40])])).

cnf(c_0_110,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_77]),c_0_100])).

cnf(c_0_111,plain,
    ( k10_relat_1(X1,k2_relat_1(k5_relat_1(X2,X1))) = k2_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_112,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_95]),c_0_95]),c_0_65]),c_0_95]),c_0_55]),c_0_55])])).

fof(c_0_113,plain,(
    ! [X9,X10] :
      ( ( ~ v5_relat_1(X10,X9)
        | r1_tarski(k2_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k2_relat_1(X10),X9)
        | v5_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_114,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_115,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(k2_relat_1(X23),X22)
      | k5_relat_1(X23,k6_relat_1(X22)) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_116,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_40])).

cnf(c_0_117,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

fof(c_0_118,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k7_relset_1(X39,X40,X41,X42) = k9_relat_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_119,plain,(
    ! [X47,X48,X49] :
      ( ( k7_relset_1(X47,X48,X49,X47) = k2_relset_1(X47,X48,X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( k8_relset_1(X47,X48,X49,X48) = k1_relset_1(X47,X48,X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_120,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(k2_funct_1(X2))
    | k2_funct_1(k5_relat_1(X1,X2)) != k2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_106]),c_0_107]),c_0_107]),c_0_108]),c_0_108])).

cnf(c_0_121,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(sr,[status(thm)],[c_0_109,c_0_110])).

fof(c_0_122,plain,(
    ! [X30] :
      ( ( k2_relat_1(X30) = k1_relat_1(k2_funct_1(X30))
        | ~ v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( k1_relat_1(X30) = k2_relat_1(k2_funct_1(X30))
        | ~ v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_123,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0
    | ~ r1_tarski(k2_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_54]),c_0_112]),c_0_38]),c_0_99]),c_0_65]),c_0_55]),c_0_56])])).

cnf(c_0_124,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_125,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_40])).

cnf(c_0_126,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_127,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_116]),c_0_56])])).

cnf(c_0_128,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_117,c_0_63])).

cnf(c_0_129,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_130,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_131,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k2_funct_1(esk3_0))) = k2_funct_1(esk3_0)
    | k1_relat_1(k2_funct_1(esk3_0)) != k2_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_54]),c_0_38]),c_0_39]),c_0_99]),c_0_121]),c_0_55]),c_0_56])])).

cnf(c_0_132,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_133,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125]),c_0_56])])).

cnf(c_0_134,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(X3)) = k7_relat_1(X1,X2)
    | ~ r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_94])).

cnf(c_0_135,negated_conjecture,
    ( k9_relat_1(esk3_0,esk1_0) = k2_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_127]),c_0_56])])).

cnf(c_0_136,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk1_0)
    | esk1_0 = k1_xboole_0
    | k2_relset_1(esk1_0,esk1_0,esk3_0) != esk1_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_40]),c_0_66]),c_0_39])]),c_0_109])).

cnf(c_0_137,plain,
    ( k2_relset_1(X1,X2,X3) = k9_relat_1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_138,negated_conjecture,
    ( k6_relat_1(esk1_0) = k2_funct_1(esk3_0)
    | k2_relat_1(k2_funct_1(esk2_0)) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133]),c_0_133]),c_0_39]),c_0_121]),c_0_56])])).

cnf(c_0_139,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_140,negated_conjecture,
    ( k5_relat_1(esk3_0,k6_relat_1(X1)) = esk3_0
    | ~ r1_tarski(k2_relat_1(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_127]),c_0_135]),c_0_56])])).

cnf(c_0_141,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk1_0)
    | k2_relat_1(esk3_0) != esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_135]),c_0_40])]),c_0_110])).

cnf(c_0_142,negated_conjecture,
    ( k6_relat_1(esk1_0) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_65]),c_0_38]),c_0_99]),c_0_55])])).

cnf(c_0_143,negated_conjecture,
    ( k5_relat_1(esk3_0,k6_relat_1(X1)) = esk3_0
    | ~ v5_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_124]),c_0_56])])).

cnf(c_0_144,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_133])])).

cnf(c_0_145,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_142])).

cnf(c_0_146,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_142]),c_0_144]),c_0_142]),c_0_125])])).

cnf(c_0_147,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_148,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_90]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:28:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.029 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 0.20/0.40  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.40  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.20/0.40  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.40  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 0.20/0.40  fof(t44_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 0.20/0.40  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.40  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.40  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.40  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.20/0.40  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.40  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 0.20/0.40  fof(t164_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 0.20/0.40  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 0.20/0.40  fof(t66_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 0.20/0.40  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.20/0.40  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.20/0.40  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.40  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.20/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.20/0.40  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.20/0.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.40  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.20/0.40  fof(c_0_29, plain, ![X43, X44, X45, X46]:((~r2_relset_1(X43,X44,X45,X46)|X45=X46|(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(X45!=X46|r2_relset_1(X43,X44,X45,X46)|(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.40  fof(c_0_30, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)&v2_funct_1(esk2_0))&~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.20/0.40  cnf(c_0_31, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_34, plain, ![X50, X51, X52, X53, X54, X55]:((v1_funct_1(k1_partfun1(X50,X51,X52,X53,X54,X55))|(~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|~v1_funct_1(X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&(m1_subset_1(k1_partfun1(X50,X51,X52,X53,X54,X55),k1_zfmisc_1(k2_zfmisc_1(X50,X53)))|(~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|~v1_funct_1(X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.20/0.40  fof(c_0_35, plain, ![X56, X57, X58, X59, X60, X61]:(~v1_funct_1(X60)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|k1_partfun1(X56,X57,X58,X59,X60,X61)=k5_relat_1(X60,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)=esk2_0|~m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.20/0.40  cnf(c_0_37, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_41, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.40  fof(c_0_42, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.40  fof(c_0_43, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k1_relset_1(X36,X37,X38)=k1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.40  fof(c_0_44, plain, ![X71, X72]:(~v1_funct_1(X72)|~v1_funct_2(X72,X71,X71)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X71,X71)))|k1_relset_1(X71,X71,X72)=X71), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.20/0.40  fof(c_0_45, plain, ![X28, X29]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)|(k2_relat_1(X28)!=k1_relat_1(X29)|k5_relat_1(X28,X29)!=X28|X29=k6_relat_1(k1_relat_1(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).
% 0.20/0.40  cnf(c_0_46, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_33]), c_0_40])])).
% 0.20/0.40  cnf(c_0_48, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_49, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.40  cnf(c_0_50, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_51, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.40  fof(c_0_52, plain, ![X62]:k6_partfun1(X62)=k6_relat_1(X62), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.40  cnf(c_0_53, plain, (X2=k6_relat_1(k1_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (k5_relat_1(esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_38]), c_0_39]), c_0_33]), c_0_40])])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_33]), c_0_49])])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_40]), c_0_49])])).
% 0.20/0.40  cnf(c_0_57, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_59, plain, ![X20]:((k1_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))&(k2_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.40  fof(c_0_60, plain, ![X21]:(k1_relat_1(k6_relat_1(X21))=X21&k2_relat_1(k6_relat_1(X21))=X21), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.40  fof(c_0_61, plain, ![X24]:(v1_relat_1(k6_relat_1(X24))&v2_funct_1(k6_relat_1(X24))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_63, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k6_relat_1(k1_relat_1(esk2_0))=esk2_0|k1_relat_1(esk2_0)!=k2_relat_1(esk3_0)|esk3_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_38]), c_0_39]), c_0_55]), c_0_56])])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_38]), c_0_33])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_67, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.40  cnf(c_0_68, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.40  cnf(c_0_69, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (k6_relat_1(esk1_0)=esk2_0|k2_relat_1(esk3_0)!=esk1_0|esk3_0!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65])).
% 0.20/0.40  cnf(c_0_72, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_66]), c_0_39]), c_0_40])])).
% 0.20/0.40  cnf(c_0_74, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])])).
% 0.20/0.40  fof(c_0_75, plain, ![X33, X34, X35]:((v4_relat_1(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v5_relat_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (k2_relat_1(esk3_0)!=esk1_0|esk3_0!=esk2_0|~r2_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (esk3_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_56])])).
% 0.20/0.40  cnf(c_0_78, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_74])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_65]), c_0_55])])).
% 0.20/0.40  fof(c_0_80, plain, ![X18, X19]:(~v1_relat_1(X19)|~v4_relat_1(X19,X18)|X19=k7_relat_1(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.20/0.40  cnf(c_0_81, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (esk1_0!=k1_xboole_0|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), c_0_79])).
% 0.20/0.40  cnf(c_0_83, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  fof(c_0_84, plain, ![X17]:(~v1_relat_1(X17)|k10_relat_1(X17,k2_relat_1(X17))=k1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.40  fof(c_0_85, plain, ![X13, X14]:(~v1_relat_1(X14)|k2_relat_1(k7_relat_1(X14,X13))=k9_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.40  cnf(c_0_86, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, (v4_relat_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_81, c_0_33])).
% 0.20/0.40  fof(c_0_88, plain, ![X63, X64, X65, X66, X67]:((X65=k1_xboole_0|v2_funct_1(X66)|~v2_funct_1(k1_partfun1(X63,X64,X64,X65,X66,X67))|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))|(~v1_funct_1(X66)|~v1_funct_2(X66,X63,X64)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))&(X64!=k1_xboole_0|v2_funct_1(X66)|~v2_funct_1(k1_partfun1(X63,X64,X64,X65,X66,X67))|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))|(~v1_funct_1(X66)|~v1_funct_2(X66,X63,X64)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.20/0.40  cnf(c_0_89, negated_conjecture, (esk1_0!=k1_xboole_0|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_79])).
% 0.20/0.40  cnf(c_0_90, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_83])).
% 0.20/0.40  fof(c_0_91, plain, ![X26, X27]:(~v1_relat_1(X27)|~v1_funct_1(X27)|(~r1_tarski(X26,k1_relat_1(X27))|~v2_funct_1(X27)|k10_relat_1(X27,k9_relat_1(X27,X26))=X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).
% 0.20/0.40  fof(c_0_92, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|k2_relat_1(k5_relat_1(X15,X16))=k9_relat_1(X16,k2_relat_1(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.20/0.40  cnf(c_0_93, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.40  cnf(c_0_94, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.40  cnf(c_0_95, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_55])])).
% 0.20/0.40  fof(c_0_96, plain, ![X31, X32]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)|(~v2_funct_1(X31)|~v2_funct_1(X32)|k2_funct_1(k5_relat_1(X31,X32))=k5_relat_1(k2_funct_1(X32),k2_funct_1(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).
% 0.20/0.40  fof(c_0_97, plain, ![X25]:(((v1_relat_1(k2_funct_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25)|~v2_funct_1(X25)))&(v1_funct_1(k2_funct_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25)|~v2_funct_1(X25))))&(v2_funct_1(k2_funct_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25)|~v2_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.20/0.40  cnf(c_0_98, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.40  cnf(c_0_99, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_100, negated_conjecture, (esk1_0!=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.40  cnf(c_0_101, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.40  cnf(c_0_102, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.20/0.40  cnf(c_0_103, plain, (k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.40  cnf(c_0_104, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)=k2_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_55])])).
% 0.20/0.40  fof(c_0_105, plain, ![X68, X69, X70]:((k5_relat_1(X70,k2_funct_1(X70))=k6_partfun1(X68)|X69=k1_xboole_0|(k2_relset_1(X68,X69,X70)!=X69|~v2_funct_1(X70))|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))&(k5_relat_1(k2_funct_1(X70),X70)=k6_partfun1(X69)|X69=k1_xboole_0|(k2_relset_1(X68,X69,X70)!=X69|~v2_funct_1(X70))|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.20/0.40  cnf(c_0_106, plain, (k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.20/0.40  cnf(c_0_107, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.20/0.40  cnf(c_0_108, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.20/0.40  cnf(c_0_109, negated_conjecture, (esk1_0=k1_xboole_0|v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_47]), c_0_58]), c_0_66]), c_0_38]), c_0_39]), c_0_99]), c_0_33]), c_0_40])])).
% 0.20/0.40  cnf(c_0_110, negated_conjecture, (esk1_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_77]), c_0_100])).
% 0.20/0.40  cnf(c_0_111, plain, (k10_relat_1(X1,k2_relat_1(k5_relat_1(X2,X1)))=k2_relat_1(X2)|~v1_funct_1(X1)|~v2_funct_1(X1)|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.20/0.40  cnf(c_0_112, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_95]), c_0_95]), c_0_65]), c_0_95]), c_0_55]), c_0_55])])).
% 0.20/0.40  fof(c_0_113, plain, ![X9, X10]:((~v5_relat_1(X10,X9)|r1_tarski(k2_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k2_relat_1(X10),X9)|v5_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.40  cnf(c_0_114, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.40  fof(c_0_115, plain, ![X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(k2_relat_1(X23),X22)|k5_relat_1(X23,k6_relat_1(X22))=X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.20/0.40  cnf(c_0_116, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_81, c_0_40])).
% 0.20/0.40  cnf(c_0_117, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.20/0.40  fof(c_0_118, plain, ![X39, X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k7_relset_1(X39,X40,X41,X42)=k9_relat_1(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.20/0.40  fof(c_0_119, plain, ![X47, X48, X49]:((k7_relset_1(X47,X48,X49,X47)=k2_relset_1(X47,X48,X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(k8_relset_1(X47,X48,X49,X48)=k1_relset_1(X47,X48,X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.20/0.40  cnf(c_0_120, plain, (k6_relat_1(k1_relat_1(k2_funct_1(X1)))=k2_funct_1(X1)|k1_relat_1(k2_funct_1(X1))!=k2_relat_1(k2_funct_1(X2))|k2_funct_1(k5_relat_1(X1,X2))!=k2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v2_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_106]), c_0_107]), c_0_107]), c_0_108]), c_0_108])).
% 0.20/0.40  cnf(c_0_121, negated_conjecture, (v2_funct_1(esk3_0)), inference(sr,[status(thm)],[c_0_109, c_0_110])).
% 0.20/0.40  fof(c_0_122, plain, ![X30]:((k2_relat_1(X30)=k1_relat_1(k2_funct_1(X30))|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(k1_relat_1(X30)=k2_relat_1(k2_funct_1(X30))|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.40  cnf(c_0_123, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0|~r1_tarski(k2_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_54]), c_0_112]), c_0_38]), c_0_99]), c_0_65]), c_0_55]), c_0_56])])).
% 0.20/0.40  cnf(c_0_124, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.20/0.40  cnf(c_0_125, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_114, c_0_40])).
% 0.20/0.40  cnf(c_0_126, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.20/0.40  cnf(c_0_127, negated_conjecture, (k7_relat_1(esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_116]), c_0_56])])).
% 0.20/0.40  cnf(c_0_128, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_117, c_0_63])).
% 0.20/0.40  cnf(c_0_129, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.20/0.40  cnf(c_0_130, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.20/0.40  cnf(c_0_131, negated_conjecture, (k6_relat_1(k1_relat_1(k2_funct_1(esk3_0)))=k2_funct_1(esk3_0)|k1_relat_1(k2_funct_1(esk3_0))!=k2_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_54]), c_0_38]), c_0_39]), c_0_99]), c_0_121]), c_0_55]), c_0_56])])).
% 0.20/0.40  cnf(c_0_132, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_122])).
% 0.20/0.40  cnf(c_0_133, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_125]), c_0_56])])).
% 0.20/0.40  cnf(c_0_134, plain, (k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(X3))=k7_relat_1(X1,X2)|~r1_tarski(k9_relat_1(X1,X2),X3)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_126, c_0_94])).
% 0.20/0.40  cnf(c_0_135, negated_conjecture, (k9_relat_1(esk3_0,esk1_0)=k2_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_127]), c_0_56])])).
% 0.20/0.40  cnf(c_0_136, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk1_0)|esk1_0=k1_xboole_0|k2_relset_1(esk1_0,esk1_0,esk3_0)!=esk1_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_40]), c_0_66]), c_0_39])]), c_0_109])).
% 0.20/0.40  cnf(c_0_137, plain, (k2_relset_1(X1,X2,X3)=k9_relat_1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.20/0.40  cnf(c_0_138, negated_conjecture, (k6_relat_1(esk1_0)=k2_funct_1(esk3_0)|k2_relat_1(k2_funct_1(esk2_0))!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133]), c_0_133]), c_0_39]), c_0_121]), c_0_56])])).
% 0.20/0.40  cnf(c_0_139, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_122])).
% 0.20/0.40  cnf(c_0_140, negated_conjecture, (k5_relat_1(esk3_0,k6_relat_1(X1))=esk3_0|~r1_tarski(k2_relat_1(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_127]), c_0_135]), c_0_56])])).
% 0.20/0.40  cnf(c_0_141, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk1_0)|k2_relat_1(esk3_0)!=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_135]), c_0_40])]), c_0_110])).
% 0.20/0.40  cnf(c_0_142, negated_conjecture, (k6_relat_1(esk1_0)=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_65]), c_0_38]), c_0_99]), c_0_55])])).
% 0.20/0.40  cnf(c_0_143, negated_conjecture, (k5_relat_1(esk3_0,k6_relat_1(X1))=esk3_0|~v5_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_124]), c_0_56])])).
% 0.20/0.40  cnf(c_0_144, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_133])])).
% 0.20/0.40  cnf(c_0_145, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk3_0))), inference(rw,[status(thm)],[c_0_70, c_0_142])).
% 0.20/0.40  cnf(c_0_146, negated_conjecture, (k2_funct_1(esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_142]), c_0_144]), c_0_142]), c_0_125])])).
% 0.20/0.40  cnf(c_0_147, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_145, c_0_146])).
% 0.20/0.40  cnf(c_0_148, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_90]), c_0_40])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 149
% 0.20/0.40  # Proof object clause steps            : 92
% 0.20/0.40  # Proof object formula steps           : 57
% 0.20/0.40  # Proof object conjectures             : 53
% 0.20/0.40  # Proof object clause conjectures      : 50
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 41
% 0.20/0.40  # Proof object initial formulas used   : 28
% 0.20/0.40  # Proof object generating inferences   : 43
% 0.20/0.40  # Proof object simplifying inferences  : 122
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 28
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 49
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 48
% 0.20/0.40  # Processed clauses                    : 591
% 0.20/0.40  # ...of these trivial                  : 16
% 0.20/0.40  # ...subsumed                          : 266
% 0.20/0.40  # ...remaining for further processing  : 309
% 0.20/0.40  # Other redundant clauses eliminated   : 10
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 12
% 0.20/0.40  # Backward-rewritten                   : 82
% 0.20/0.40  # Generated clauses                    : 913
% 0.20/0.40  # ...of the previous two non-trivial   : 831
% 0.20/0.40  # Contextual simplify-reflections      : 20
% 0.20/0.40  # Paramodulations                      : 902
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 10
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
% 0.20/0.40  # Current number of processed clauses  : 164
% 0.20/0.40  #    Positive orientable unit clauses  : 42
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 119
% 0.20/0.40  # Current number of unprocessed clauses: 321
% 0.20/0.40  # ...number of literals in the above   : 1326
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 144
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 6938
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 3457
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 152
% 0.20/0.40  # Unit Clause-clause subsumption calls : 300
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 16
% 0.20/0.40  # BW rewrite match successes           : 13
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 18261
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.061 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.067 s
% 0.20/0.40  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
