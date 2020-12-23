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
% DateTime   : Thu Dec  3 11:02:59 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  152 (2356 expanded)
%              Number of clauses        :  107 (1020 expanded)
%              Number of leaves         :   22 ( 562 expanded)
%              Depth                    :   19
%              Number of atoms          :  380 (11230 expanded)
%              Number of equality atoms :  119 (3329 expanded)
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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(c_0_22,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_23,negated_conjecture,(
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

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ( ~ v4_relat_1(X10,X9)
        | r1_tarski(k1_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k1_relat_1(X10),X9)
        | v4_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | v1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_27,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_28,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
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

fof(c_0_33,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | k2_relat_1(k7_relat_1(X12,X11)) = k9_relat_1(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_34,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ v4_relat_1(X16,X15)
      | X16 = k7_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_35,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X24] :
      ( ( v1_relat_1(k2_funct_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( v1_funct_1(k2_funct_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_39,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v4_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v4_relat_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_43,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_36])])).

fof(c_0_46,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_relset_1(X39,X40,X41) = k2_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_47,plain,
    ( v4_relat_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(esk3_0) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_52,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),X1)
    | ~ r1_tarski(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_36])])).

fof(c_0_55,plain,(
    ! [X52] :
      ( v1_partfun1(k6_partfun1(X52),X52)
      & m1_subset_1(k6_partfun1(X52),k1_zfmisc_1(k2_zfmisc_1(X52,X52))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_56,plain,(
    ! [X59] : k6_partfun1(X59) = k6_relat_1(X59) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_51])).

fof(c_0_58,plain,(
    ! [X36,X37,X38] :
      ( ( v4_relat_1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v5_relat_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_59,plain,(
    ! [X53,X54,X55,X56,X57,X58] :
      ( ~ v1_funct_1(X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ v1_funct_1(X58)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | k1_partfun1(X53,X54,X55,X56,X57,X58) = k5_relat_1(X57,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_31]),c_0_53]),c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

fof(c_0_62,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k1_relat_1(k5_relat_1(X13,X14)) = k10_relat_1(X13,k1_relat_1(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_63,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_65,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(k2_relat_1(X23),X22)
      | k5_relat_1(X23,k6_relat_1(X22)) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_66,negated_conjecture,
    ( v4_relat_1(esk4_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_57])).

cnf(c_0_67,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_69,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_72,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k2_funct_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_61])).

cnf(c_0_73,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_75,plain,(
    ! [X20] :
      ( k1_relat_1(k6_relat_1(X20)) = X20
      & k2_relat_1(k6_relat_1(X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_76,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk4_0,X1)) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_57])).

cnf(c_0_78,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_66]),c_0_57])])).

cnf(c_0_79,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

fof(c_0_80,plain,(
    ! [X42,X43,X44,X45] :
      ( ( ~ r2_relset_1(X42,X43,X44,X45)
        | X44 = X45
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != X45
        | r2_relset_1(X42,X43,X44,X45)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_81,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_60])).

fof(c_0_84,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ( v1_funct_1(k1_partfun1(X46,X47,X48,X49,X50,X51))
        | ~ v1_funct_1(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( m1_subset_1(k1_partfun1(X46,X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(X46,X49)))
        | ~ v1_funct_1(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_85,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k5_relat_1(k5_relat_1(X17,X18),X19) = k5_relat_1(X17,k5_relat_1(X18,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_86,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(X1),X2)) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_43])).

cnf(c_0_87,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_43]),c_0_50]),c_0_36])])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk4_0,X1)) = k10_relat_1(esk4_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_57])).

cnf(c_0_89,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_74])).

cnf(c_0_90,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_91,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_29])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(esk4_0) = k9_relat_1(esk4_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_93,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_79]),c_0_57])])).

cnf(c_0_94,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_95,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_60]),c_0_60])).

cnf(c_0_96,negated_conjecture,
    ( k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_50])])).

cnf(c_0_97,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_98,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_99,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k5_relat_1(k6_relat_1(k1_relat_1(X21)),X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_100,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_101,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_50]),c_0_36])])).

cnf(c_0_102,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_103,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1))) = k10_relat_1(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_104,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(k9_relat_1(esk4_0,k1_relat_1(esk4_0)))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_57]),c_0_92])).

cnf(c_0_105,negated_conjecture,
    ( k9_relat_1(esk4_0,esk2_0) = k9_relat_1(esk4_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_93]),c_0_92]),c_0_57])])).

cnf(c_0_106,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_107,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_31])).

cnf(c_0_108,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_74])).

cnf(c_0_109,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_70]),c_0_71])])).

cnf(c_0_111,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),X2) = k5_relat_1(X1,k5_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_36])).

cnf(c_0_112,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_113,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_49]),c_0_50]),c_0_36])])).

fof(c_0_114,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | ~ r1_tarski(X25,k2_relat_1(X26))
      | k9_relat_1(X26,k10_relat_1(X26,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_79]),c_0_57])])).

cnf(c_0_116,negated_conjecture,
    ( k10_relat_1(esk4_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0))) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_117,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_relat_1(esk4_0)) = k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_105,c_0_60])).

cnf(c_0_118,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_119,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_106]),c_0_89])])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_107]),c_0_36])])).

cnf(c_0_121,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_83]),c_0_96]),c_0_50])])).

cnf(c_0_123,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0) = k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_57])).

cnf(c_0_124,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_112,c_0_36])).

cnf(c_0_125,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_113])).

fof(c_0_126,plain,(
    ! [X31] :
      ( ( k5_relat_1(X31,k2_funct_1(X31)) = k6_relat_1(k1_relat_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( k5_relat_1(k2_funct_1(X31),X31) = k6_relat_1(k2_relat_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_127,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_115,c_0_60])).

cnf(c_0_129,negated_conjecture,
    ( k1_relat_1(esk4_0) = k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_130,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_57])).

cnf(c_0_131,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(esk1_0)) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_132,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122])])).

cnf(c_0_133,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k5_relat_1(esk3_0,esk4_0)) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_89])])).

cnf(c_0_134,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)) = k2_funct_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_125])).

cnf(c_0_135,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_136,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_48]),c_0_50]),c_0_36])])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_138,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_130,c_0_129])).

cnf(c_0_139,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132]),c_0_133])).

cnf(c_0_140,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)) = k2_funct_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_43]),c_0_50]),c_0_36])])).

cnf(c_0_141,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_135]),c_0_48]),c_0_49]),c_0_50]),c_0_36])])).

cnf(c_0_142,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_112,c_0_57])).

cnf(c_0_143,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))) = k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_144,negated_conjecture,
    ( k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_139]),c_0_90])).

cnf(c_0_145,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(esk1_0)) = k2_funct_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_120])).

cnf(c_0_146,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_43]),c_0_50]),c_0_36])])).

cnf(c_0_147,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))),esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_142,c_0_129])).

cnf(c_0_148,negated_conjecture,
    ( k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_149,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0) = k2_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_132]),c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_151,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148]),c_0_149]),c_0_150]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:23:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.10/1.26  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 1.10/1.26  # and selection function SelectNewComplexAHP.
% 1.10/1.26  #
% 1.10/1.26  # Preprocessing time       : 0.023 s
% 1.10/1.26  
% 1.10/1.26  # Proof found!
% 1.10/1.26  # SZS status Theorem
% 1.10/1.26  # SZS output start CNFRefutation
% 1.10/1.26  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.10/1.26  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 1.10/1.26  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.10/1.26  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.10/1.26  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 1.10/1.26  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.10/1.26  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.10/1.26  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.10/1.26  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.10/1.26  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.10/1.26  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.10/1.26  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.10/1.26  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 1.10/1.26  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 1.10/1.26  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.10/1.26  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.10/1.26  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.10/1.26  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 1.10/1.26  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 1.10/1.26  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 1.10/1.26  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 1.10/1.26  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.10/1.26  fof(c_0_22, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.10/1.26  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 1.10/1.26  fof(c_0_24, plain, ![X9, X10]:((~v4_relat_1(X10,X9)|r1_tarski(k1_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k1_relat_1(X10),X9)|v4_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.10/1.26  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.10/1.26  fof(c_0_26, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.10/1.26  fof(c_0_27, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.10/1.26  cnf(c_0_28, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.10/1.26  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 1.10/1.26  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.10/1.26  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  fof(c_0_32, plain, ![X30]:((k2_relat_1(X30)=k1_relat_1(k2_funct_1(X30))|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(k1_relat_1(X30)=k2_relat_1(k2_funct_1(X30))|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 1.10/1.26  fof(c_0_33, plain, ![X11, X12]:(~v1_relat_1(X12)|k2_relat_1(k7_relat_1(X12,X11))=k9_relat_1(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 1.10/1.26  fof(c_0_34, plain, ![X15, X16]:(~v1_relat_1(X16)|~v4_relat_1(X16,X15)|X16=k7_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 1.10/1.26  cnf(c_0_35, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.10/1.26  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.10/1.26  cnf(c_0_37, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.10/1.26  fof(c_0_38, plain, ![X24]:((v1_relat_1(k2_funct_1(X24))|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(v1_funct_1(k2_funct_1(X24))|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.10/1.26  cnf(c_0_39, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.10/1.26  cnf(c_0_40, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.10/1.26  cnf(c_0_41, negated_conjecture, (v4_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.10/1.26  cnf(c_0_42, plain, (v4_relat_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 1.10/1.26  cnf(c_0_43, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.10/1.26  cnf(c_0_44, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 1.10/1.26  cnf(c_0_45, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_36])])).
% 1.10/1.26  fof(c_0_46, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k2_relset_1(X39,X40,X41)=k2_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.10/1.26  cnf(c_0_47, plain, (v4_relat_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.10/1.26  cnf(c_0_48, negated_conjecture, (k2_relat_1(esk3_0)=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.10/1.26  cnf(c_0_49, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  cnf(c_0_52, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.10/1.26  cnf(c_0_53, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  cnf(c_0_54, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),X1)|~r1_tarski(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_36])])).
% 1.10/1.26  fof(c_0_55, plain, ![X52]:(v1_partfun1(k6_partfun1(X52),X52)&m1_subset_1(k6_partfun1(X52),k1_zfmisc_1(k2_zfmisc_1(X52,X52)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 1.10/1.26  fof(c_0_56, plain, ![X59]:k6_partfun1(X59)=k6_relat_1(X59), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 1.10/1.26  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_51])).
% 1.10/1.26  fof(c_0_58, plain, ![X36, X37, X38]:((v4_relat_1(X38,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v5_relat_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.10/1.26  fof(c_0_59, plain, ![X53, X54, X55, X56, X57, X58]:(~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))|k1_partfun1(X53,X54,X55,X56,X57,X58)=k5_relat_1(X57,X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 1.10/1.26  cnf(c_0_60, negated_conjecture, (esk2_0=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_31]), c_0_53]), c_0_48])).
% 1.10/1.26  cnf(c_0_61, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 1.10/1.26  fof(c_0_62, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|k1_relat_1(k5_relat_1(X13,X14))=k10_relat_1(X13,k1_relat_1(X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 1.10/1.26  cnf(c_0_63, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.10/1.26  cnf(c_0_64, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.10/1.26  fof(c_0_65, plain, ![X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(k2_relat_1(X23),X22)|k5_relat_1(X23,k6_relat_1(X22))=X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 1.10/1.26  cnf(c_0_66, negated_conjecture, (v4_relat_1(esk4_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_57])).
% 1.10/1.26  cnf(c_0_67, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.10/1.26  cnf(c_0_68, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  cnf(c_0_69, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.10/1.26  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0)))), inference(rw,[status(thm)],[c_0_51, c_0_60])).
% 1.10/1.26  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  cnf(c_0_72, negated_conjecture, (k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_61])).
% 1.10/1.26  cnf(c_0_73, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.10/1.26  cnf(c_0_74, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 1.10/1.26  fof(c_0_75, plain, ![X20]:(k1_relat_1(k6_relat_1(X20))=X20&k2_relat_1(k6_relat_1(X20))=X20), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.10/1.26  cnf(c_0_76, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.10/1.26  cnf(c_0_77, negated_conjecture, (k2_relat_1(k7_relat_1(esk4_0,X1))=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_57])).
% 1.10/1.26  cnf(c_0_78, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_66]), c_0_57])])).
% 1.10/1.26  cnf(c_0_79, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 1.10/1.26  fof(c_0_80, plain, ![X42, X43, X44, X45]:((~r2_relset_1(X42,X43,X44,X45)|X44=X45|(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&(X44!=X45|r2_relset_1(X42,X43,X44,X45)|(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 1.10/1.26  cnf(c_0_81, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_68, c_0_64])).
% 1.10/1.26  cnf(c_0_82, negated_conjecture, (k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 1.10/1.26  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))), inference(rw,[status(thm)],[c_0_31, c_0_60])).
% 1.10/1.26  fof(c_0_84, plain, ![X46, X47, X48, X49, X50, X51]:((v1_funct_1(k1_partfun1(X46,X47,X48,X49,X50,X51))|(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&(m1_subset_1(k1_partfun1(X46,X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(X46,X49)))|(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 1.10/1.26  fof(c_0_85, plain, ![X17, X18, X19]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|(~v1_relat_1(X19)|k5_relat_1(k5_relat_1(X17,X18),X19)=k5_relat_1(X17,k5_relat_1(X18,X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 1.10/1.26  cnf(c_0_86, plain, (k2_relat_1(k7_relat_1(k2_funct_1(X1),X2))=k9_relat_1(k2_funct_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_43])).
% 1.10/1.26  cnf(c_0_87, negated_conjecture, (k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_43]), c_0_50]), c_0_36])])).
% 1.10/1.26  cnf(c_0_88, negated_conjecture, (k1_relat_1(k5_relat_1(esk4_0,X1))=k10_relat_1(esk4_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_57])).
% 1.10/1.26  cnf(c_0_89, plain, (v1_relat_1(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_74])).
% 1.10/1.26  cnf(c_0_90, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.10/1.26  cnf(c_0_91, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_29])).
% 1.10/1.26  cnf(c_0_92, negated_conjecture, (k2_relat_1(esk4_0)=k9_relat_1(esk4_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.10/1.26  cnf(c_0_93, negated_conjecture, (k7_relat_1(esk4_0,esk2_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_79]), c_0_57])])).
% 1.10/1.26  cnf(c_0_94, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.10/1.26  cnf(c_0_95, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_60]), c_0_60])).
% 1.10/1.26  cnf(c_0_96, negated_conjecture, (k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_50])])).
% 1.10/1.26  cnf(c_0_97, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.10/1.26  cnf(c_0_98, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.10/1.26  fof(c_0_99, plain, ![X21]:(~v1_relat_1(X21)|k5_relat_1(k6_relat_1(k1_relat_1(X21)),X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 1.10/1.26  cnf(c_0_100, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.10/1.26  cnf(c_0_101, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_50]), c_0_36])])).
% 1.10/1.26  cnf(c_0_102, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.10/1.26  cnf(c_0_103, negated_conjecture, (k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1)))=k10_relat_1(esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 1.10/1.26  cnf(c_0_104, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(k9_relat_1(esk4_0,k1_relat_1(esk4_0))))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_57]), c_0_92])).
% 1.10/1.26  cnf(c_0_105, negated_conjecture, (k9_relat_1(esk4_0,esk2_0)=k9_relat_1(esk4_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_93]), c_0_92]), c_0_57])])).
% 1.10/1.26  cnf(c_0_106, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.10/1.26  cnf(c_0_107, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_67, c_0_31])).
% 1.10/1.26  cnf(c_0_108, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_94, c_0_74])).
% 1.10/1.26  cnf(c_0_109, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 1.10/1.26  cnf(c_0_110, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_70]), c_0_71])])).
% 1.10/1.26  cnf(c_0_111, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),X2)=k5_relat_1(X1,k5_relat_1(esk3_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_98, c_0_36])).
% 1.10/1.26  cnf(c_0_112, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 1.10/1.26  cnf(c_0_113, negated_conjecture, (k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_49]), c_0_50]), c_0_36])])).
% 1.10/1.26  fof(c_0_114, plain, ![X25, X26]:(~v1_relat_1(X26)|~v1_funct_1(X26)|(~r1_tarski(X25,k2_relat_1(X26))|k9_relat_1(X26,k10_relat_1(X26,X25))=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 1.10/1.26  cnf(c_0_115, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_79]), c_0_57])])).
% 1.10/1.26  cnf(c_0_116, negated_conjecture, (k10_relat_1(esk4_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 1.10/1.26  cnf(c_0_117, negated_conjecture, (k9_relat_1(esk4_0,k1_relat_1(esk4_0))=k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_105, c_0_60])).
% 1.10/1.26  cnf(c_0_118, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_36])).
% 1.10/1.26  cnf(c_0_119, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_106]), c_0_89])])).
% 1.10/1.26  cnf(c_0_120, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_107]), c_0_36])])).
% 1.10/1.26  cnf(c_0_121, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 1.10/1.26  cnf(c_0_122, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_83]), c_0_96]), c_0_50])])).
% 1.10/1.26  cnf(c_0_123, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0)=k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_111, c_0_57])).
% 1.10/1.26  cnf(c_0_124, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_112, c_0_36])).
% 1.10/1.26  cnf(c_0_125, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_101, c_0_113])).
% 1.10/1.26  fof(c_0_126, plain, ![X31]:((k5_relat_1(X31,k2_funct_1(X31))=k6_relat_1(k1_relat_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(k5_relat_1(k2_funct_1(X31),X31)=k6_relat_1(k2_relat_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 1.10/1.26  cnf(c_0_127, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 1.10/1.26  cnf(c_0_128, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_115, c_0_60])).
% 1.10/1.26  cnf(c_0_129, negated_conjecture, (k1_relat_1(esk4_0)=k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))), inference(rw,[status(thm)],[c_0_116, c_0_117])).
% 1.10/1.26  cnf(c_0_130, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_118, c_0_57])).
% 1.10/1.26  cnf(c_0_131, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(esk1_0))=k6_relat_1(k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 1.10/1.26  cnf(c_0_132, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122])])).
% 1.10/1.26  cnf(c_0_133, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k5_relat_1(esk3_0,esk4_0))=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_89])])).
% 1.10/1.26  cnf(c_0_134, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))=k2_funct_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_76, c_0_125])).
% 1.10/1.26  cnf(c_0_135, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_126])).
% 1.10/1.26  cnf(c_0_136, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_48]), c_0_50]), c_0_36])])).
% 1.10/1.26  cnf(c_0_137, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_128, c_0_129])).
% 1.10/1.26  cnf(c_0_138, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))), inference(rw,[status(thm)],[c_0_130, c_0_129])).
% 1.10/1.26  cnf(c_0_139, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_132]), c_0_133])).
% 1.10/1.26  cnf(c_0_140, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))=k2_funct_1(esk3_0)|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_43]), c_0_50]), c_0_36])])).
% 1.10/1.26  cnf(c_0_141, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_135]), c_0_48]), c_0_49]), c_0_50]), c_0_36])])).
% 1.10/1.26  cnf(c_0_142, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_112, c_0_57])).
% 1.10/1.26  cnf(c_0_143, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))))=k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 1.10/1.26  cnf(c_0_144, negated_conjecture, (k10_relat_1(esk3_0,k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_139]), c_0_90])).
% 1.10/1.26  cnf(c_0_145, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(esk1_0))=k2_funct_1(esk3_0)), inference(spm,[status(thm)],[c_0_140, c_0_120])).
% 1.10/1.26  cnf(c_0_146, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_43]), c_0_50]), c_0_36])])).
% 1.10/1.26  cnf(c_0_147, negated_conjecture, (k5_relat_1(k6_relat_1(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))),esk4_0)=esk4_0), inference(rw,[status(thm)],[c_0_142, c_0_129])).
% 1.10/1.26  cnf(c_0_148, negated_conjecture, (k10_relat_1(esk4_0,k9_relat_1(esk4_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_143, c_0_144])).
% 1.10/1.26  cnf(c_0_149, negated_conjecture, (k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)=k2_funct_1(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_132]), c_0_146])).
% 1.10/1.26  cnf(c_0_150, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.10/1.26  cnf(c_0_151, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_148]), c_0_149]), c_0_150]), ['proof']).
% 1.10/1.26  # SZS output end CNFRefutation
% 1.10/1.26  # Proof object total steps             : 152
% 1.10/1.26  # Proof object clause steps            : 107
% 1.10/1.26  # Proof object formula steps           : 45
% 1.10/1.26  # Proof object conjectures             : 76
% 1.10/1.26  # Proof object clause conjectures      : 73
% 1.10/1.26  # Proof object formula conjectures     : 3
% 1.10/1.26  # Proof object initial clauses used    : 32
% 1.10/1.26  # Proof object initial formulas used   : 22
% 1.10/1.26  # Proof object generating inferences   : 55
% 1.10/1.26  # Proof object simplifying inferences  : 85
% 1.10/1.26  # Training examples: 0 positive, 0 negative
% 1.10/1.26  # Parsed axioms                        : 26
% 1.10/1.26  # Removed by relevancy pruning/SinE    : 0
% 1.10/1.26  # Initial clauses                      : 49
% 1.10/1.26  # Removed in clause preprocessing      : 1
% 1.10/1.26  # Initial clauses in saturation        : 48
% 1.10/1.26  # Processed clauses                    : 7549
% 1.10/1.26  # ...of these trivial                  : 247
% 1.10/1.26  # ...subsumed                          : 4496
% 1.10/1.26  # ...remaining for further processing  : 2806
% 1.10/1.26  # Other redundant clauses eliminated   : 3
% 1.10/1.26  # Clauses deleted for lack of memory   : 0
% 1.10/1.26  # Backward-subsumed                    : 315
% 1.10/1.26  # Backward-rewritten                   : 617
% 1.10/1.26  # Generated clauses                    : 67554
% 1.10/1.26  # ...of the previous two non-trivial   : 61219
% 1.10/1.26  # Contextual simplify-reflections      : 0
% 1.10/1.26  # Paramodulations                      : 67543
% 1.10/1.26  # Factorizations                       : 0
% 1.10/1.26  # Equation resolutions                 : 11
% 1.10/1.26  # Propositional unsat checks           : 0
% 1.10/1.26  #    Propositional check models        : 0
% 1.10/1.26  #    Propositional check unsatisfiable : 0
% 1.10/1.26  #    Propositional clauses             : 0
% 1.10/1.26  #    Propositional clauses after purity: 0
% 1.10/1.26  #    Propositional unsat core size     : 0
% 1.10/1.26  #    Propositional preprocessing time  : 0.000
% 1.10/1.26  #    Propositional encoding time       : 0.000
% 1.10/1.26  #    Propositional solver time         : 0.000
% 1.10/1.26  #    Success case prop preproc time    : 0.000
% 1.10/1.26  #    Success case prop encoding time   : 0.000
% 1.10/1.26  #    Success case prop solver time     : 0.000
% 1.10/1.26  # Current number of processed clauses  : 1871
% 1.10/1.26  #    Positive orientable unit clauses  : 113
% 1.10/1.26  #    Positive unorientable unit clauses: 0
% 1.10/1.26  #    Negative unit clauses             : 3
% 1.10/1.26  #    Non-unit-clauses                  : 1755
% 1.10/1.26  # Current number of unprocessed clauses: 52955
% 1.10/1.26  # ...number of literals in the above   : 319585
% 1.10/1.26  # Current number of archived formulas  : 0
% 1.10/1.26  # Current number of archived clauses   : 933
% 1.10/1.26  # Clause-clause subsumption calls (NU) : 145193
% 1.10/1.26  # Rec. Clause-clause subsumption calls : 51212
% 1.10/1.26  # Non-unit clause-clause subsumptions  : 4811
% 1.10/1.26  # Unit Clause-clause subsumption calls : 4128
% 1.10/1.26  # Rewrite failures with RHS unbound    : 0
% 1.10/1.26  # BW rewrite match attempts            : 187
% 1.10/1.26  # BW rewrite match successes           : 89
% 1.10/1.26  # Condensation attempts                : 0
% 1.10/1.26  # Condensation successes               : 0
% 1.10/1.26  # Termbank termtop insertions          : 1876504
% 1.10/1.26  
% 1.10/1.26  # -------------------------------------------------
% 1.10/1.26  # User time                : 0.876 s
% 1.10/1.26  # System time              : 0.040 s
% 1.10/1.26  # Total time               : 0.916 s
% 1.10/1.26  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
