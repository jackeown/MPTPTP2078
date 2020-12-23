%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:15 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  156 (2688 expanded)
%              Number of clauses        :  107 (1124 expanded)
%              Number of leaves         :   24 ( 676 expanded)
%              Depth                    :   18
%              Number of atoms          :  384 (11911 expanded)
%              Number of equality atoms :  119 (3314 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t36_funct_2,conjecture,(
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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

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

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

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

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(c_0_24,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
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
    inference(assume_negation,[status(cth)],[t36_funct_2])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_29,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))
    & v2_funct_1(esk3_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk4_0 != k2_funct_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_30,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_31,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_37,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ v4_relat_1(X20,X19)
      | X20 = k7_relat_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_38,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_40,plain,(
    ! [X28] :
      ( ( v1_relat_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_41,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v4_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X34] :
      ( ( k2_relat_1(X34) = k1_relat_1(k2_funct_1(X34))
        | ~ v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( k1_relat_1(X34) = k2_relat_1(k2_funct_1(X34))
        | ~ v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_46,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k2_relset_1(X40,X41,X42) = k2_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_39])])).

cnf(c_0_49,plain,
    ( v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_50,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk3_0) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_51]),c_0_35])])).

fof(c_0_59,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_60,plain,(
    ! [X60] : k6_partfun1(X60) = k6_relat_1(X60) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_61,plain,(
    ! [X54,X55,X56,X57,X58,X59] :
      ( ~ v1_funct_1(X58)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | ~ v1_funct_1(X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | k1_partfun1(X54,X55,X56,X57,X58,X59) = k5_relat_1(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_53]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_56]),c_0_57]),c_0_39])])).

fof(c_0_64,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | k1_relat_1(k5_relat_1(X17,X18)) = k10_relat_1(X17,k1_relat_1(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_65,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(k2_relat_1(X27),X26)
      | k5_relat_1(X27,k6_relat_1(X26)) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_66,negated_conjecture,
    ( v4_relat_1(esk4_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_58])).

cnf(c_0_67,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_68,plain,(
    ! [X53] :
      ( v1_partfun1(k6_partfun1(X53),X53)
      & m1_subset_1(k6_partfun1(X53),k1_zfmisc_1(k2_zfmisc_1(X53,X53))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_69,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_70,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k2_funct_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_63])).

cnf(c_0_75,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_76,plain,(
    ! [X29] :
      ( v1_relat_1(k6_relat_1(X29))
      & v2_funct_1(k6_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_77,plain,(
    ! [X24] :
      ( k1_relat_1(k6_relat_1(X24)) = X24
      & k2_relat_1(k6_relat_1(X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_78,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk4_0,X1)) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_66]),c_0_58])])).

cnf(c_0_81,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

fof(c_0_82,plain,(
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

cnf(c_0_83,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_85,negated_conjecture,
    ( k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_62])).

fof(c_0_87,plain,(
    ! [X47,X48,X49,X50,X51,X52] :
      ( ( v1_funct_1(k1_partfun1(X47,X48,X49,X50,X51,X52))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( m1_subset_1(k1_partfun1(X47,X48,X49,X50,X51,X52),k1_zfmisc_1(k2_zfmisc_1(X47,X50)))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_88,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | k5_relat_1(k5_relat_1(X21,X22),X23) = k5_relat_1(X21,k5_relat_1(X22,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_89,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(X1),X2)) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_90,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_44]),c_0_57]),c_0_39])])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk4_0,X1)) = k10_relat_1(esk4_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_58])).

cnf(c_0_92,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_93,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_94,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_32])).

cnf(c_0_95,negated_conjecture,
    ( k2_relat_1(esk4_0) = k9_relat_1(esk4_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_96,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_81]),c_0_58])])).

cnf(c_0_97,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_98,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_70])).

cnf(c_0_99,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_62]),c_0_62])).

cnf(c_0_100,negated_conjecture,
    ( k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_57])])).

cnf(c_0_101,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_102,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_103,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | k5_relat_1(k6_relat_1(k1_relat_1(X25)),X25) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_104,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_105,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_57]),c_0_39])])).

cnf(c_0_106,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1))) = k10_relat_1(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_108,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(k9_relat_1(esk4_0,k1_relat_1(esk4_0)))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_58]),c_0_95])).

cnf(c_0_109,negated_conjecture,
    ( k9_relat_1(esk4_0,esk2_0) = k9_relat_1(esk4_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_96]),c_0_95]),c_0_58])])).

cnf(c_0_110,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_111,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_34])).

cnf(c_0_112,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_113,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_72]),c_0_73])])).

cnf(c_0_115,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),X2) = k5_relat_1(X1,k5_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_39])).

cnf(c_0_116,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_117,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_56]),c_0_57]),c_0_39])])).

fof(c_0_118,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ r1_tarski(X30,k2_relat_1(X31))
      | k9_relat_1(X31,k10_relat_1(X31,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_81]),c_0_58])])).

cnf(c_0_120,negated_conjecture,
    ( k10_relat_1(esk4_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0))) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_121,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_relat_1(esk4_0)) = k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_109,c_0_62])).

cnf(c_0_122,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_39])).

cnf(c_0_123,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_110]),c_0_92])])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_111]),c_0_39])])).

cnf(c_0_125,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_86]),c_0_100]),c_0_57])])).

cnf(c_0_127,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0) = k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_58])).

cnf(c_0_128,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_39])).

cnf(c_0_129,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_117])).

fof(c_0_130,plain,(
    ! [X35] :
      ( ( k5_relat_1(X35,k2_funct_1(X35)) = k6_relat_1(k1_relat_1(X35))
        | ~ v2_funct_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( k5_relat_1(k2_funct_1(X35),X35) = k6_relat_1(k2_relat_1(X35))
        | ~ v2_funct_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_131,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_119,c_0_62])).

cnf(c_0_133,negated_conjecture,
    ( k1_relat_1(esk4_0) = k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_134,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_58])).

cnf(c_0_135,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(esk1_0)) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_136,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126])])).

cnf(c_0_137,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k5_relat_1(esk3_0,esk4_0)) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_92])])).

cnf(c_0_138,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)) = k2_funct_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_129])).

cnf(c_0_139,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_140,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_54]),c_0_57]),c_0_39])])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_142,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_134,c_0_133])).

cnf(c_0_143,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136]),c_0_137])).

cnf(c_0_144,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)) = k2_funct_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_44]),c_0_57]),c_0_39])])).

cnf(c_0_145,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_139]),c_0_54]),c_0_56]),c_0_57]),c_0_39])])).

cnf(c_0_146,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_58])).

cnf(c_0_147,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))) = k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_148,negated_conjecture,
    ( k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143]),c_0_93])).

cnf(c_0_149,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(esk1_0)) = k2_funct_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_124])).

cnf(c_0_150,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_44]),c_0_57]),c_0_39])])).

cnf(c_0_151,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))),esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_146,c_0_133])).

cnf(c_0_152,negated_conjecture,
    ( k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_153,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0) = k2_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_136]),c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_155,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_152]),c_0_153]),c_0_154]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:58:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.19/1.40  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 1.19/1.40  # and selection function SelectNewComplexAHP.
% 1.19/1.40  #
% 1.19/1.40  # Preprocessing time       : 0.029 s
% 1.19/1.40  
% 1.19/1.40  # Proof found!
% 1.19/1.40  # SZS status Theorem
% 1.19/1.40  # SZS output start CNFRefutation
% 1.19/1.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.19/1.40  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 1.19/1.40  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.19/1.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.19/1.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.19/1.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.19/1.40  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.19/1.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.19/1.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 1.19/1.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.19/1.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.19/1.40  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.19/1.40  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 1.19/1.40  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 1.19/1.40  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.19/1.40  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.19/1.40  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.19/1.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.19/1.40  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.19/1.40  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 1.19/1.40  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 1.19/1.40  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 1.19/1.40  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 1.19/1.40  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.19/1.40  fof(c_0_24, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.19/1.40  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 1.19/1.40  fof(c_0_26, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.19/1.40  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.19/1.40  fof(c_0_28, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.19/1.40  fof(c_0_29, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 1.19/1.40  fof(c_0_30, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.19/1.40  cnf(c_0_31, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.19/1.40  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 1.19/1.40  cnf(c_0_33, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.19/1.40  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.19/1.40  fof(c_0_36, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 1.19/1.40  fof(c_0_37, plain, ![X19, X20]:(~v1_relat_1(X20)|~v4_relat_1(X20,X19)|X20=k7_relat_1(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 1.19/1.40  cnf(c_0_38, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.19/1.40  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 1.19/1.40  fof(c_0_40, plain, ![X28]:((v1_relat_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.19/1.40  cnf(c_0_41, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.19/1.40  cnf(c_0_42, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.19/1.40  cnf(c_0_43, negated_conjecture, (v4_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.19/1.40  cnf(c_0_44, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.19/1.40  fof(c_0_45, plain, ![X34]:((k2_relat_1(X34)=k1_relat_1(k2_funct_1(X34))|~v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(k1_relat_1(X34)=k2_relat_1(k2_funct_1(X34))|~v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 1.19/1.40  fof(c_0_46, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k2_relset_1(X40,X41,X42)=k2_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.19/1.40  cnf(c_0_47, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 1.19/1.40  cnf(c_0_48, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_39])])).
% 1.19/1.40  cnf(c_0_49, plain, (v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_44])).
% 1.19/1.40  cnf(c_0_50, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.19/1.40  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_52, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.19/1.40  cnf(c_0_53, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_54, negated_conjecture, (k2_relat_1(esk3_0)=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.19/1.40  cnf(c_0_55, plain, (v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.19/1.40  cnf(c_0_56, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_51]), c_0_35])])).
% 1.19/1.40  fof(c_0_59, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.19/1.40  fof(c_0_60, plain, ![X60]:k6_partfun1(X60)=k6_relat_1(X60), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 1.19/1.40  fof(c_0_61, plain, ![X54, X55, X56, X57, X58, X59]:(~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|~v1_funct_1(X59)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|k1_partfun1(X54,X55,X56,X57,X58,X59)=k5_relat_1(X58,X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 1.19/1.40  cnf(c_0_62, negated_conjecture, (esk2_0=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_34]), c_0_53]), c_0_54])).
% 1.19/1.40  cnf(c_0_63, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_54]), c_0_56]), c_0_57]), c_0_39])])).
% 1.19/1.40  fof(c_0_64, plain, ![X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|k1_relat_1(k5_relat_1(X17,X18))=k10_relat_1(X17,k1_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 1.19/1.40  fof(c_0_65, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(k2_relat_1(X27),X26)|k5_relat_1(X27,k6_relat_1(X26))=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 1.19/1.40  cnf(c_0_66, negated_conjecture, (v4_relat_1(esk4_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_58])).
% 1.19/1.40  cnf(c_0_67, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.19/1.40  fof(c_0_68, plain, ![X53]:(v1_partfun1(k6_partfun1(X53),X53)&m1_subset_1(k6_partfun1(X53),k1_zfmisc_1(k2_zfmisc_1(X53,X53)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 1.19/1.40  cnf(c_0_69, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_70, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.19/1.40  cnf(c_0_71, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.19/1.40  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0)))), inference(rw,[status(thm)],[c_0_51, c_0_62])).
% 1.19/1.40  cnf(c_0_73, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_74, negated_conjecture, (k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_63])).
% 1.19/1.40  cnf(c_0_75, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.19/1.40  fof(c_0_76, plain, ![X29]:(v1_relat_1(k6_relat_1(X29))&v2_funct_1(k6_relat_1(X29))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 1.19/1.40  fof(c_0_77, plain, ![X24]:(k1_relat_1(k6_relat_1(X24))=X24&k2_relat_1(k6_relat_1(X24))=X24), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.19/1.40  cnf(c_0_78, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.19/1.40  cnf(c_0_79, negated_conjecture, (k2_relat_1(k7_relat_1(esk4_0,X1))=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_58])).
% 1.19/1.40  cnf(c_0_80, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_66]), c_0_58])])).
% 1.19/1.40  cnf(c_0_81, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 1.19/1.40  fof(c_0_82, plain, ![X43, X44, X45, X46]:((~r2_relset_1(X43,X44,X45,X46)|X45=X46|(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(X45!=X46|r2_relset_1(X43,X44,X45,X46)|(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 1.19/1.40  cnf(c_0_83, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.19/1.40  cnf(c_0_84, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 1.19/1.40  cnf(c_0_85, negated_conjecture, (k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 1.19/1.40  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))), inference(rw,[status(thm)],[c_0_34, c_0_62])).
% 1.19/1.40  fof(c_0_87, plain, ![X47, X48, X49, X50, X51, X52]:((v1_funct_1(k1_partfun1(X47,X48,X49,X50,X51,X52))|(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&(m1_subset_1(k1_partfun1(X47,X48,X49,X50,X51,X52),k1_zfmisc_1(k2_zfmisc_1(X47,X50)))|(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 1.19/1.40  fof(c_0_88, plain, ![X21, X22, X23]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|(~v1_relat_1(X23)|k5_relat_1(k5_relat_1(X21,X22),X23)=k5_relat_1(X21,k5_relat_1(X22,X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 1.19/1.40  cnf(c_0_89, plain, (k2_relat_1(k7_relat_1(k2_funct_1(X1),X2))=k9_relat_1(k2_funct_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 1.19/1.40  cnf(c_0_90, negated_conjecture, (k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_44]), c_0_57]), c_0_39])])).
% 1.19/1.40  cnf(c_0_91, negated_conjecture, (k1_relat_1(k5_relat_1(esk4_0,X1))=k10_relat_1(esk4_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_58])).
% 1.19/1.40  cnf(c_0_92, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.19/1.40  cnf(c_0_93, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.19/1.40  cnf(c_0_94, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_78, c_0_32])).
% 1.19/1.40  cnf(c_0_95, negated_conjecture, (k2_relat_1(esk4_0)=k9_relat_1(esk4_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 1.19/1.40  cnf(c_0_96, negated_conjecture, (k7_relat_1(esk4_0,esk2_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_81]), c_0_58])])).
% 1.19/1.40  cnf(c_0_97, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.19/1.40  cnf(c_0_98, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_83, c_0_70])).
% 1.19/1.40  cnf(c_0_99, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_62]), c_0_62])).
% 1.19/1.40  cnf(c_0_100, negated_conjecture, (k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_57])])).
% 1.19/1.40  cnf(c_0_101, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 1.19/1.40  cnf(c_0_102, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 1.19/1.40  fof(c_0_103, plain, ![X25]:(~v1_relat_1(X25)|k5_relat_1(k6_relat_1(k1_relat_1(X25)),X25)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 1.19/1.40  cnf(c_0_104, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.19/1.40  cnf(c_0_105, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_57]), c_0_39])])).
% 1.19/1.40  cnf(c_0_106, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.19/1.40  cnf(c_0_107, negated_conjecture, (k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1)))=k10_relat_1(esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 1.19/1.40  cnf(c_0_108, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(k9_relat_1(esk4_0,k1_relat_1(esk4_0))))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_58]), c_0_95])).
% 1.19/1.40  cnf(c_0_109, negated_conjecture, (k9_relat_1(esk4_0,esk2_0)=k9_relat_1(esk4_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_96]), c_0_95]), c_0_58])])).
% 1.19/1.40  cnf(c_0_110, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.19/1.40  cnf(c_0_111, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_67, c_0_34])).
% 1.19/1.40  cnf(c_0_112, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 1.19/1.40  cnf(c_0_113, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_99, c_0_100])).
% 1.19/1.40  cnf(c_0_114, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_72]), c_0_73])])).
% 1.19/1.40  cnf(c_0_115, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),X2)=k5_relat_1(X1,k5_relat_1(esk3_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_39])).
% 1.19/1.40  cnf(c_0_116, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.19/1.40  cnf(c_0_117, negated_conjecture, (k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_56]), c_0_57]), c_0_39])])).
% 1.19/1.40  fof(c_0_118, plain, ![X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~r1_tarski(X30,k2_relat_1(X31))|k9_relat_1(X31,k10_relat_1(X31,X30))=X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 1.19/1.40  cnf(c_0_119, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_81]), c_0_58])])).
% 1.19/1.40  cnf(c_0_120, negated_conjecture, (k10_relat_1(esk4_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 1.19/1.40  cnf(c_0_121, negated_conjecture, (k9_relat_1(esk4_0,k1_relat_1(esk4_0))=k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_109, c_0_62])).
% 1.19/1.40  cnf(c_0_122, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_39])).
% 1.19/1.40  cnf(c_0_123, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_110]), c_0_92])])).
% 1.19/1.40  cnf(c_0_124, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_111]), c_0_39])])).
% 1.19/1.40  cnf(c_0_125, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 1.19/1.40  cnf(c_0_126, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_86]), c_0_100]), c_0_57])])).
% 1.19/1.40  cnf(c_0_127, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0)=k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_115, c_0_58])).
% 1.19/1.40  cnf(c_0_128, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_116, c_0_39])).
% 1.19/1.40  cnf(c_0_129, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_105, c_0_117])).
% 1.19/1.40  fof(c_0_130, plain, ![X35]:((k5_relat_1(X35,k2_funct_1(X35))=k6_relat_1(k1_relat_1(X35))|~v2_funct_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(k5_relat_1(k2_funct_1(X35),X35)=k6_relat_1(k2_relat_1(X35))|~v2_funct_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 1.19/1.40  cnf(c_0_131, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 1.19/1.40  cnf(c_0_132, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_119, c_0_62])).
% 1.19/1.40  cnf(c_0_133, negated_conjecture, (k1_relat_1(esk4_0)=k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))), inference(rw,[status(thm)],[c_0_120, c_0_121])).
% 1.19/1.40  cnf(c_0_134, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_122, c_0_58])).
% 1.19/1.40  cnf(c_0_135, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(esk1_0))=k6_relat_1(k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 1.19/1.40  cnf(c_0_136, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126])])).
% 1.19/1.40  cnf(c_0_137, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k5_relat_1(esk3_0,esk4_0))=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_92])])).
% 1.19/1.40  cnf(c_0_138, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))=k2_funct_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_78, c_0_129])).
% 1.19/1.40  cnf(c_0_139, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_130])).
% 1.19/1.40  cnf(c_0_140, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_54]), c_0_57]), c_0_39])])).
% 1.19/1.40  cnf(c_0_141, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_132, c_0_133])).
% 1.19/1.40  cnf(c_0_142, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))), inference(rw,[status(thm)],[c_0_134, c_0_133])).
% 1.19/1.40  cnf(c_0_143, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136]), c_0_137])).
% 1.19/1.40  cnf(c_0_144, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))=k2_funct_1(esk3_0)|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_44]), c_0_57]), c_0_39])])).
% 1.19/1.40  cnf(c_0_145, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_139]), c_0_54]), c_0_56]), c_0_57]), c_0_39])])).
% 1.19/1.40  cnf(c_0_146, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_116, c_0_58])).
% 1.19/1.40  cnf(c_0_147, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))))=k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))), inference(spm,[status(thm)],[c_0_140, c_0_141])).
% 1.19/1.40  cnf(c_0_148, negated_conjecture, (k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_143]), c_0_93])).
% 1.19/1.40  cnf(c_0_149, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(esk1_0))=k2_funct_1(esk3_0)), inference(spm,[status(thm)],[c_0_144, c_0_124])).
% 1.19/1.40  cnf(c_0_150, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_44]), c_0_57]), c_0_39])])).
% 1.19/1.40  cnf(c_0_151, negated_conjecture, (k5_relat_1(k6_relat_1(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))),esk4_0)=esk4_0), inference(rw,[status(thm)],[c_0_146, c_0_133])).
% 1.19/1.40  cnf(c_0_152, negated_conjecture, (k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_147, c_0_148])).
% 1.19/1.40  cnf(c_0_153, negated_conjecture, (k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)=k2_funct_1(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_136]), c_0_150])).
% 1.19/1.40  cnf(c_0_154, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.19/1.40  cnf(c_0_155, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_152]), c_0_153]), c_0_154]), ['proof']).
% 1.19/1.40  # SZS output end CNFRefutation
% 1.19/1.40  # Proof object total steps             : 156
% 1.19/1.40  # Proof object clause steps            : 107
% 1.19/1.40  # Proof object formula steps           : 49
% 1.19/1.40  # Proof object conjectures             : 75
% 1.19/1.40  # Proof object clause conjectures      : 72
% 1.19/1.40  # Proof object formula conjectures     : 3
% 1.19/1.40  # Proof object initial clauses used    : 34
% 1.19/1.40  # Proof object initial formulas used   : 24
% 1.19/1.40  # Proof object generating inferences   : 53
% 1.19/1.40  # Proof object simplifying inferences  : 89
% 1.19/1.40  # Training examples: 0 positive, 0 negative
% 1.19/1.40  # Parsed axioms                        : 27
% 1.19/1.40  # Removed by relevancy pruning/SinE    : 0
% 1.19/1.40  # Initial clauses                      : 51
% 1.19/1.40  # Removed in clause preprocessing      : 1
% 1.19/1.40  # Initial clauses in saturation        : 50
% 1.19/1.40  # Processed clauses                    : 8980
% 1.19/1.40  # ...of these trivial                  : 297
% 1.19/1.40  # ...subsumed                          : 5319
% 1.19/1.40  # ...remaining for further processing  : 3364
% 1.19/1.40  # Other redundant clauses eliminated   : 5
% 1.19/1.40  # Clauses deleted for lack of memory   : 0
% 1.19/1.40  # Backward-subsumed                    : 377
% 1.19/1.40  # Backward-rewritten                   : 744
% 1.19/1.40  # Generated clauses                    : 86202
% 1.19/1.40  # ...of the previous two non-trivial   : 77989
% 1.19/1.40  # Contextual simplify-reflections      : 0
% 1.19/1.40  # Paramodulations                      : 86186
% 1.19/1.40  # Factorizations                       : 0
% 1.19/1.40  # Equation resolutions                 : 16
% 1.19/1.40  # Propositional unsat checks           : 0
% 1.19/1.40  #    Propositional check models        : 0
% 1.19/1.40  #    Propositional check unsatisfiable : 0
% 1.19/1.40  #    Propositional clauses             : 0
% 1.19/1.40  #    Propositional clauses after purity: 0
% 1.19/1.40  #    Propositional unsat core size     : 0
% 1.19/1.40  #    Propositional preprocessing time  : 0.000
% 1.19/1.40  #    Propositional encoding time       : 0.000
% 1.19/1.40  #    Propositional solver time         : 0.000
% 1.19/1.40  #    Success case prop preproc time    : 0.000
% 1.19/1.40  #    Success case prop encoding time   : 0.000
% 1.19/1.40  #    Success case prop solver time     : 0.000
% 1.19/1.40  # Current number of processed clauses  : 2240
% 1.19/1.40  #    Positive orientable unit clauses  : 177
% 1.19/1.40  #    Positive unorientable unit clauses: 0
% 1.19/1.40  #    Negative unit clauses             : 3
% 1.19/1.40  #    Non-unit-clauses                  : 2060
% 1.19/1.40  # Current number of unprocessed clauses: 68176
% 1.19/1.40  # ...number of literals in the above   : 403235
% 1.19/1.40  # Current number of archived formulas  : 0
% 1.19/1.40  # Current number of archived clauses   : 1122
% 1.19/1.40  # Clause-clause subsumption calls (NU) : 245397
% 1.19/1.40  # Rec. Clause-clause subsumption calls : 84540
% 1.19/1.40  # Non-unit clause-clause subsumptions  : 5696
% 1.19/1.40  # Unit Clause-clause subsumption calls : 6141
% 1.19/1.40  # Rewrite failures with RHS unbound    : 0
% 1.19/1.40  # BW rewrite match attempts            : 238
% 1.19/1.40  # BW rewrite match successes           : 103
% 1.19/1.40  # Condensation attempts                : 0
% 1.19/1.40  # Condensation successes               : 0
% 1.19/1.40  # Termbank termtop insertions          : 2441958
% 1.19/1.41  
% 1.19/1.41  # -------------------------------------------------
% 1.19/1.41  # User time                : 1.019 s
% 1.19/1.41  # System time              : 0.051 s
% 1.19/1.41  # Total time               : 1.070 s
% 1.19/1.41  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
