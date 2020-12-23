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
% DateTime   : Thu Dec  3 11:05:58 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  143 (1743 expanded)
%              Number of clauses        :   92 ( 605 expanded)
%              Number of leaves         :   25 ( 441 expanded)
%              Depth                    :   16
%              Number of atoms          :  481 (10812 expanded)
%              Number of equality atoms :  130 ( 380 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(dt_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k2_funct_2(X1,X2))
        & v1_funct_2(k2_funct_2(X1,X2),X1,X1)
        & v3_funct_2(k2_funct_2(X1,X2),X1,X1)
        & m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(c_0_25,negated_conjecture,(
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

fof(c_0_26,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_relat_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_27,plain,(
    ! [X76,X77] :
      ( ( v1_funct_1(k2_funct_2(X76,X77))
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X76,X76)
        | ~ v3_funct_2(X77,X76,X76)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76))) )
      & ( v1_funct_2(k2_funct_2(X76,X77),X76,X76)
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X76,X76)
        | ~ v3_funct_2(X77,X76,X76)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76))) )
      & ( v3_funct_2(k2_funct_2(X76,X77),X76,X76)
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X76,X76)
        | ~ v3_funct_2(X77,X76,X76)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76))) )
      & ( m1_subset_1(k2_funct_2(X76,X77),k1_zfmisc_1(k2_zfmisc_1(X76,X76)))
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X76,X76)
        | ~ v3_funct_2(X77,X76,X76)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

fof(c_0_28,plain,(
    ! [X24,X25] : v1_relat_1(k2_zfmisc_1(X24,X25)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_29,plain,(
    ! [X62,X63,X64] :
      ( ( v1_funct_1(X64)
        | ~ v1_funct_1(X64)
        | ~ v3_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v2_funct_1(X64)
        | ~ v1_funct_1(X64)
        | ~ v3_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v2_funct_2(X64,X63)
        | ~ v1_funct_1(X64)
        | ~ v3_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_30,plain,(
    ! [X85,X86] :
      ( ~ v1_funct_1(X86)
      | ~ v1_funct_2(X86,X85,X85)
      | ~ v3_funct_2(X86,X85,X85)
      | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X85,X85)))
      | k2_funct_2(X85,X86) = k2_funct_1(X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_31,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk2_0,esk2_0)
    & v3_funct_2(esk3_0,esk2_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk2_0)
    & v3_funct_2(esk4_0,esk2_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0))
    & ~ r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_32,plain,(
    ! [X41,X42,X43] :
      ( ( v4_relat_1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v5_relat_1(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_33,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v3_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v3_funct_2(esk4_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v1_relat_1(k2_funct_2(X1,X2))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_46,plain,(
    ! [X68,X69] :
      ( ( ~ v2_funct_2(X69,X68)
        | k2_relat_1(X69) = X68
        | ~ v1_relat_1(X69)
        | ~ v5_relat_1(X69,X68) )
      & ( k2_relat_1(X69) != X68
        | v2_funct_2(X69,X68)
        | ~ v1_relat_1(X69)
        | ~ v5_relat_1(X69,X68) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_47,negated_conjecture,
    ( v3_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( v2_funct_2(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34]),c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( k2_funct_2(esk2_0,esk4_0) = k2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_52,plain,
    ( v5_relat_1(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(k2_funct_2(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_55,plain,(
    ! [X33] :
      ( ( k1_relat_1(X33) != k1_xboole_0
        | X33 = k1_xboole_0
        | ~ v1_relat_1(X33) )
      & ( k2_relat_1(X33) != k1_xboole_0
        | X33 = k1_xboole_0
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_56,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( v2_funct_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_58,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_49]),c_0_35])])).

cnf(c_0_60,negated_conjecture,
    ( v2_funct_2(k2_funct_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_41]),c_0_40]),c_0_42]),c_0_43])])).

cnf(c_0_61,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_41]),c_0_40]),c_0_42]),c_0_43])])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_51])).

fof(c_0_63,plain,(
    ! [X87] : k6_partfun1(X87) = k6_relat_1(X87) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_64,plain,(
    ! [X78] :
      ( v1_partfun1(k6_partfun1(X78),X78)
      & m1_subset_1(k6_partfun1(X78),k1_zfmisc_1(k2_zfmisc_1(X78,X78))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_66,negated_conjecture,
    ( k2_funct_2(esk2_0,esk3_0) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_54]),c_0_48]),c_0_49])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59])])).

fof(c_0_69,plain,(
    ! [X36] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ v2_funct_1(X36)
      | k2_funct_1(k2_funct_1(X36)) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_70,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_71,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_72,plain,(
    ! [X51,X52,X53,X54] :
      ( ( ~ r2_relset_1(X51,X52,X53,X54)
        | X53 = X54
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X53 != X54
        | r2_relset_1(X51,X52,X53,X54)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_73,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_74,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_76,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k1_relset_1(X44,X45,X46) = k1_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_77,plain,(
    ! [X65,X66,X67] :
      ( ( ~ v1_funct_2(X67,X65,X66)
        | X65 = k1_relset_1(X65,X66,X67)
        | X66 = k1_xboole_0
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( X65 != k1_relset_1(X65,X66,X67)
        | v1_funct_2(X67,X65,X66)
        | X66 = k1_xboole_0
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( ~ v1_funct_2(X67,X65,X66)
        | X65 = k1_relset_1(X65,X66,X67)
        | X65 != k1_xboole_0
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( X65 != k1_relset_1(X65,X66,X67)
        | v1_funct_2(X67,X65,X66)
        | X65 != k1_xboole_0
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( ~ v1_funct_2(X67,X65,X66)
        | X67 = k1_xboole_0
        | X65 = k1_xboole_0
        | X66 != k1_xboole_0
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( X67 != k1_xboole_0
        | v1_funct_2(X67,X65,X66)
        | X65 = k1_xboole_0
        | X66 != k1_xboole_0
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_59])])).

cnf(c_0_80,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( k2_funct_1(esk4_0) = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_70]),c_0_62])])).

cnf(c_0_82,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_40]),c_0_42]),c_0_43])])).

cnf(c_0_83,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_43]),c_0_35])])).

cnf(c_0_84,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_74])).

fof(c_0_87,plain,(
    ! [X70,X71,X72,X73,X74,X75] :
      ( ( v1_funct_1(k1_partfun1(X70,X71,X72,X73,X74,X75))
        | ~ v1_funct_1(X74)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | ~ v1_funct_1(X75)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) )
      & ( m1_subset_1(k1_partfun1(X70,X71,X72,X73,X74,X75),k1_zfmisc_1(k2_zfmisc_1(X70,X73)))
        | ~ v1_funct_1(X74)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | ~ v1_funct_1(X75)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_88,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k5_relat_1(X35,k6_relat_1(k2_relat_1(X35))) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_89,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | k5_relat_1(k5_relat_1(X30,X31),X32) = k5_relat_1(X30,k5_relat_1(X31,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_90,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_91,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_93,negated_conjecture,
    ( k2_funct_1(k1_xboole_0) = esk4_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_42]),c_0_83])])).

cnf(c_0_94,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_95,plain,(
    ! [X79,X80,X81,X82,X83,X84] :
      ( ~ v1_funct_1(X83)
      | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X79,X80)))
      | ~ v1_funct_1(X84)
      | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X81,X82)))
      | k1_partfun1(X79,X80,X81,X82,X83,X84) = k5_relat_1(X83,X84) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_96,negated_conjecture,
    ( k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_97,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_98,plain,(
    ! [X88,X89,X90] :
      ( ( k5_relat_1(X90,k2_funct_1(X90)) = k6_partfun1(X88)
        | X89 = k1_xboole_0
        | k2_relset_1(X88,X89,X90) != X89
        | ~ v2_funct_1(X90)
        | ~ v1_funct_1(X90)
        | ~ v1_funct_2(X90,X88,X89)
        | ~ m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89))) )
      & ( k5_relat_1(k2_funct_1(X90),X90) = k6_partfun1(X89)
        | X89 = k1_xboole_0
        | k2_relset_1(X88,X89,X90) != X89
        | ~ v2_funct_1(X90)
        | ~ v1_funct_1(X90)
        | ~ v1_funct_2(X90,X88,X89)
        | ~ m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_99,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k7_relset_1(X47,X48,X49,X50) = k9_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_100,plain,(
    ! [X56,X57,X58] :
      ( ( k7_relset_1(X56,X57,X58,X56) = k2_relset_1(X56,X57,X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( k8_relset_1(X56,X57,X58,X57) = k1_relset_1(X56,X57,X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_101,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v4_relat_1(X29,X28)
      | X29 = k7_relat_1(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_102,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_103,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_104,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_105,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_86]),c_0_35])])).

fof(c_0_106,plain,(
    ! [X34] :
      ( ~ v1_relat_1(X34)
      | k5_relat_1(k6_relat_1(k1_relat_1(X34)),X34) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_107,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_108,plain,
    ( v1_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_109,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ r2_relset_1(esk2_0,esk2_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_110,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_94])).

cnf(c_0_111,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_112,negated_conjecture,
    ( k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_42]),c_0_48]),c_0_43]),c_0_49])])).

cnf(c_0_113,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_114,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_115,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

fof(c_0_116,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k2_relat_1(k7_relat_1(X27,X26)) = k9_relat_1(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_117,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_118,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_43])).

cnf(c_0_119,negated_conjecture,
    ( v2_funct_2(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_40]),c_0_42]),c_0_43])])).

cnf(c_0_120,negated_conjecture,
    ( v5_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_121,plain,
    ( k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(k2_relat_1(k5_relat_1(X1,X2))))) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])])).

cnf(c_0_122,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_123,plain,
    ( k1_relat_1(k2_funct_2(X1,X2)) = X1
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_34])).

cnf(c_0_124,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_43])])).

cnf(c_0_125,negated_conjecture,
    ( k6_relat_1(esk2_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_42]),c_0_48]),c_0_43]),c_0_49])])).

cnf(c_0_126,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_113,c_0_74])).

cnf(c_0_127,plain,
    ( k2_relset_1(X1,X2,X3) = k9_relat_1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_128,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_129,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_83])])).

cnf(c_0_130,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_119]),c_0_120]),c_0_83])])).

cnf(c_0_131,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))) = X1
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_105])])).

cnf(c_0_132,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_40]),c_0_51]),c_0_41]),c_0_42]),c_0_43])]),c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),k5_relat_1(esk3_0,esk4_0)) = k2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_70]),c_0_125]),c_0_62])])).

cnf(c_0_134,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | X3 = k1_xboole_0
    | k9_relat_1(X1,X2) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_135,negated_conjecture,
    ( k9_relat_1(esk4_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130]),c_0_83])])).

cnf(c_0_136,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk3_0,esk4_0),k2_funct_1(esk4_0)) = k2_funct_1(esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_70]),c_0_125]),c_0_62])]),c_0_132]),c_0_125]),c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k5_relat_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_41]),c_0_125]),c_0_135]),c_0_82]),c_0_42]),c_0_43])]),c_0_124])).

cnf(c_0_138,negated_conjecture,
    ( k5_relat_1(esk3_0,k5_relat_1(esk3_0,esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_68]),c_0_59])]),c_0_125])).

cnf(c_0_139,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_136]),c_0_137]),c_0_138]),c_0_62]),c_0_83]),c_0_59])])).

cnf(c_0_140,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_139]),c_0_82]),c_0_42]),c_0_83])])).

cnf(c_0_141,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_140])).

cnf(c_0_142,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_110]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.04/3.22  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 3.04/3.22  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.04/3.22  #
% 3.04/3.22  # Preprocessing time       : 0.040 s
% 3.04/3.22  
% 3.04/3.22  # Proof found!
% 3.04/3.22  # SZS status Theorem
% 3.04/3.22  # SZS output start CNFRefutation
% 3.04/3.22  fof(t87_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 3.04/3.22  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.04/3.22  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 3.04/3.22  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.04/3.22  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.04/3.22  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.04/3.22  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.04/3.22  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.04/3.22  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.04/3.22  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.04/3.22  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.04/3.22  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.04/3.22  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.04/3.22  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.04/3.22  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.04/3.22  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.04/3.22  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.04/3.22  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.04/3.22  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.04/3.22  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 3.04/3.22  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.04/3.22  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.04/3.22  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.04/3.22  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 3.04/3.22  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.04/3.22  fof(c_0_25, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)))))), inference(assume_negation,[status(cth)],[t87_funct_2])).
% 3.04/3.22  fof(c_0_26, plain, ![X21, X22]:(~v1_relat_1(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_relat_1(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 3.04/3.22  fof(c_0_27, plain, ![X76, X77]:((((v1_funct_1(k2_funct_2(X76,X77))|(~v1_funct_1(X77)|~v1_funct_2(X77,X76,X76)|~v3_funct_2(X77,X76,X76)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76)))))&(v1_funct_2(k2_funct_2(X76,X77),X76,X76)|(~v1_funct_1(X77)|~v1_funct_2(X77,X76,X76)|~v3_funct_2(X77,X76,X76)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76))))))&(v3_funct_2(k2_funct_2(X76,X77),X76,X76)|(~v1_funct_1(X77)|~v1_funct_2(X77,X76,X76)|~v3_funct_2(X77,X76,X76)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76))))))&(m1_subset_1(k2_funct_2(X76,X77),k1_zfmisc_1(k2_zfmisc_1(X76,X76)))|(~v1_funct_1(X77)|~v1_funct_2(X77,X76,X76)|~v3_funct_2(X77,X76,X76)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X76,X76)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 3.04/3.22  fof(c_0_28, plain, ![X24, X25]:v1_relat_1(k2_zfmisc_1(X24,X25)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 3.04/3.22  fof(c_0_29, plain, ![X62, X63, X64]:(((v1_funct_1(X64)|(~v1_funct_1(X64)|~v3_funct_2(X64,X62,X63))|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(v2_funct_1(X64)|(~v1_funct_1(X64)|~v3_funct_2(X64,X62,X63))|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&(v2_funct_2(X64,X63)|(~v1_funct_1(X64)|~v3_funct_2(X64,X62,X63))|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 3.04/3.22  fof(c_0_30, plain, ![X85, X86]:(~v1_funct_1(X86)|~v1_funct_2(X86,X85,X85)|~v3_funct_2(X86,X85,X85)|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X85,X85)))|k2_funct_2(X85,X86)=k2_funct_1(X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 3.04/3.22  fof(c_0_31, negated_conjecture, ((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&v3_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&((((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk2_0))&v3_funct_2(esk4_0,esk2_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&(r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0))&~r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 3.04/3.22  fof(c_0_32, plain, ![X41, X42, X43]:((v4_relat_1(X43,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(v5_relat_1(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 3.04/3.22  cnf(c_0_33, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.04/3.22  cnf(c_0_34, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.04/3.22  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.04/3.22  cnf(c_0_36, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.04/3.22  cnf(c_0_37, plain, (v3_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.04/3.22  cnf(c_0_38, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.04/3.22  cnf(c_0_39, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.04/3.22  cnf(c_0_40, negated_conjecture, (v3_funct_2(esk4_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_44, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.04/3.22  cnf(c_0_45, plain, (v1_relat_1(k2_funct_2(X1,X2))|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 3.04/3.22  fof(c_0_46, plain, ![X68, X69]:((~v2_funct_2(X69,X68)|k2_relat_1(X69)=X68|(~v1_relat_1(X69)|~v5_relat_1(X69,X68)))&(k2_relat_1(X69)!=X68|v2_funct_2(X69,X68)|(~v1_relat_1(X69)|~v5_relat_1(X69,X68)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 3.04/3.22  cnf(c_0_47, negated_conjecture, (v3_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_50, plain, (v2_funct_2(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_34]), c_0_38])).
% 3.04/3.22  cnf(c_0_51, negated_conjecture, (k2_funct_2(esk2_0,esk4_0)=k2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43])])).
% 3.04/3.22  cnf(c_0_52, plain, (v5_relat_1(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 3.04/3.22  cnf(c_0_53, negated_conjecture, (v1_relat_1(k2_funct_2(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_41]), c_0_42]), c_0_43])])).
% 3.04/3.22  cnf(c_0_54, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  fof(c_0_55, plain, ![X33]:((k1_relat_1(X33)!=k1_xboole_0|X33=k1_xboole_0|~v1_relat_1(X33))&(k2_relat_1(X33)!=k1_xboole_0|X33=k1_xboole_0|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 3.04/3.22  cnf(c_0_56, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.04/3.22  cnf(c_0_57, negated_conjecture, (v2_funct_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_48]), c_0_49])])).
% 3.04/3.22  cnf(c_0_58, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_49])).
% 3.04/3.22  cnf(c_0_59, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_49]), c_0_35])])).
% 3.04/3.22  cnf(c_0_60, negated_conjecture, (v2_funct_2(k2_funct_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_41]), c_0_40]), c_0_42]), c_0_43])])).
% 3.04/3.22  cnf(c_0_61, negated_conjecture, (v5_relat_1(k2_funct_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_51]), c_0_41]), c_0_40]), c_0_42]), c_0_43])])).
% 3.04/3.22  cnf(c_0_62, negated_conjecture, (v1_relat_1(k2_funct_1(esk4_0))), inference(rw,[status(thm)],[c_0_53, c_0_51])).
% 3.04/3.22  fof(c_0_63, plain, ![X87]:k6_partfun1(X87)=k6_relat_1(X87), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 3.04/3.22  fof(c_0_64, plain, ![X78]:(v1_partfun1(k6_partfun1(X78),X78)&m1_subset_1(k6_partfun1(X78),k1_zfmisc_1(k2_zfmisc_1(X78,X78)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 3.04/3.22  cnf(c_0_65, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_66, negated_conjecture, (k2_funct_2(esk2_0,esk3_0)=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_54]), c_0_48]), c_0_49])])).
% 3.04/3.22  cnf(c_0_67, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 3.04/3.22  cnf(c_0_68, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59])])).
% 3.04/3.22  fof(c_0_69, plain, ![X36]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~v2_funct_1(X36)|k2_funct_1(k2_funct_1(X36))=X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 3.04/3.22  cnf(c_0_70, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_60]), c_0_61]), c_0_62])])).
% 3.04/3.22  cnf(c_0_71, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.04/3.22  fof(c_0_72, plain, ![X51, X52, X53, X54]:((~r2_relset_1(X51,X52,X53,X54)|X53=X54|(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(X53!=X54|r2_relset_1(X51,X52,X53,X54)|(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 3.04/3.22  cnf(c_0_73, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.04/3.22  cnf(c_0_74, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 3.04/3.22  cnf(c_0_75, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 3.04/3.22  fof(c_0_76, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k1_relset_1(X44,X45,X46)=k1_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 3.04/3.22  fof(c_0_77, plain, ![X65, X66, X67]:((((~v1_funct_2(X67,X65,X66)|X65=k1_relset_1(X65,X66,X67)|X66=k1_xboole_0|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))&(X65!=k1_relset_1(X65,X66,X67)|v1_funct_2(X67,X65,X66)|X66=k1_xboole_0|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))&((~v1_funct_2(X67,X65,X66)|X65=k1_relset_1(X65,X66,X67)|X65!=k1_xboole_0|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))&(X65!=k1_relset_1(X65,X66,X67)|v1_funct_2(X67,X65,X66)|X65!=k1_xboole_0|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))))&((~v1_funct_2(X67,X65,X66)|X67=k1_xboole_0|X65=k1_xboole_0|X66!=k1_xboole_0|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))&(X67!=k1_xboole_0|v1_funct_2(X67,X65,X66)|X65=k1_xboole_0|X66!=k1_xboole_0|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 3.04/3.22  cnf(c_0_78, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_1(esk3_0))), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 3.04/3.22  cnf(c_0_79, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_59])])).
% 3.04/3.22  cnf(c_0_80, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 3.04/3.22  cnf(c_0_81, negated_conjecture, (k2_funct_1(esk4_0)=k1_xboole_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_70]), c_0_62])])).
% 3.04/3.22  cnf(c_0_82, negated_conjecture, (v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_40]), c_0_42]), c_0_43])])).
% 3.04/3.22  cnf(c_0_83, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_43]), c_0_35])])).
% 3.04/3.22  cnf(c_0_84, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 3.04/3.22  cnf(c_0_85, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 3.04/3.22  cnf(c_0_86, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_75, c_0_74])).
% 3.04/3.22  fof(c_0_87, plain, ![X70, X71, X72, X73, X74, X75]:((v1_funct_1(k1_partfun1(X70,X71,X72,X73,X74,X75))|(~v1_funct_1(X74)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|~v1_funct_1(X75)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))))&(m1_subset_1(k1_partfun1(X70,X71,X72,X73,X74,X75),k1_zfmisc_1(k2_zfmisc_1(X70,X73)))|(~v1_funct_1(X74)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|~v1_funct_1(X75)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 3.04/3.22  fof(c_0_88, plain, ![X35]:(~v1_relat_1(X35)|k5_relat_1(X35,k6_relat_1(k2_relat_1(X35)))=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 3.04/3.22  fof(c_0_89, plain, ![X30, X31, X32]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|(~v1_relat_1(X32)|k5_relat_1(k5_relat_1(X30,X31),X32)=k5_relat_1(X30,k5_relat_1(X31,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 3.04/3.22  cnf(c_0_90, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 3.04/3.22  cnf(c_0_91, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 3.04/3.22  cnf(c_0_92, negated_conjecture, (esk2_0!=k1_xboole_0|~r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 3.04/3.22  cnf(c_0_93, negated_conjecture, (k2_funct_1(k1_xboole_0)=esk4_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_42]), c_0_83])])).
% 3.04/3.22  cnf(c_0_94, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 3.04/3.22  fof(c_0_95, plain, ![X79, X80, X81, X82, X83, X84]:(~v1_funct_1(X83)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X79,X80)))|~v1_funct_1(X84)|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X81,X82)))|k1_partfun1(X79,X80,X81,X82,X83,X84)=k5_relat_1(X83,X84)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 3.04/3.22  cnf(c_0_96, negated_conjecture, (k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0)=k6_relat_1(esk2_0)|~m1_subset_1(k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 3.04/3.22  cnf(c_0_97, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 3.04/3.22  fof(c_0_98, plain, ![X88, X89, X90]:((k5_relat_1(X90,k2_funct_1(X90))=k6_partfun1(X88)|X89=k1_xboole_0|(k2_relset_1(X88,X89,X90)!=X89|~v2_funct_1(X90))|(~v1_funct_1(X90)|~v1_funct_2(X90,X88,X89)|~m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89)))))&(k5_relat_1(k2_funct_1(X90),X90)=k6_partfun1(X89)|X89=k1_xboole_0|(k2_relset_1(X88,X89,X90)!=X89|~v2_funct_1(X90))|(~v1_funct_1(X90)|~v1_funct_2(X90,X88,X89)|~m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 3.04/3.22  fof(c_0_99, plain, ![X47, X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k7_relset_1(X47,X48,X49,X50)=k9_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 3.04/3.22  fof(c_0_100, plain, ![X56, X57, X58]:((k7_relset_1(X56,X57,X58,X56)=k2_relset_1(X56,X57,X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(k8_relset_1(X56,X57,X58,X57)=k1_relset_1(X56,X57,X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 3.04/3.22  fof(c_0_101, plain, ![X28, X29]:(~v1_relat_1(X29)|~v4_relat_1(X29,X28)|X29=k7_relat_1(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 3.04/3.22  cnf(c_0_102, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.04/3.22  cnf(c_0_103, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 3.04/3.22  cnf(c_0_104, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 3.04/3.22  cnf(c_0_105, plain, (v1_relat_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_86]), c_0_35])])).
% 3.04/3.22  fof(c_0_106, plain, ![X34]:(~v1_relat_1(X34)|k5_relat_1(k6_relat_1(k1_relat_1(X34)),X34)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 3.04/3.22  cnf(c_0_107, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 3.04/3.22  cnf(c_0_108, plain, (v1_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.04/3.22  cnf(c_0_109, negated_conjecture, (esk2_0!=k1_xboole_0|~r2_relset_1(esk2_0,esk2_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 3.04/3.22  cnf(c_0_110, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_94])).
% 3.04/3.22  cnf(c_0_111, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 3.04/3.22  cnf(c_0_112, negated_conjecture, (k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_42]), c_0_48]), c_0_43]), c_0_49])])).
% 3.04/3.22  cnf(c_0_113, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 3.04/3.22  cnf(c_0_114, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 3.04/3.22  cnf(c_0_115, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 3.04/3.22  fof(c_0_116, plain, ![X26, X27]:(~v1_relat_1(X27)|k2_relat_1(k7_relat_1(X27,X26))=k9_relat_1(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 3.04/3.22  cnf(c_0_117, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 3.04/3.22  cnf(c_0_118, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_102, c_0_43])).
% 3.04/3.22  cnf(c_0_119, negated_conjecture, (v2_funct_2(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_40]), c_0_42]), c_0_43])])).
% 3.04/3.22  cnf(c_0_120, negated_conjecture, (v5_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 3.04/3.22  cnf(c_0_121, plain, (k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(k2_relat_1(k5_relat_1(X1,X2)))))=k5_relat_1(X1,X2)|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])])).
% 3.04/3.22  cnf(c_0_122, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 3.04/3.22  cnf(c_0_123, plain, (k1_relat_1(k2_funct_2(X1,X2))=X1|X1=k1_xboole_0|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_34])).
% 3.04/3.22  cnf(c_0_124, negated_conjecture, (esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_43])])).
% 3.04/3.22  cnf(c_0_125, negated_conjecture, (k6_relat_1(esk2_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_42]), c_0_48]), c_0_43]), c_0_49])])).
% 3.04/3.22  cnf(c_0_126, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_113, c_0_74])).
% 3.04/3.22  cnf(c_0_127, plain, (k2_relset_1(X1,X2,X3)=k9_relat_1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 3.04/3.22  cnf(c_0_128, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 3.04/3.22  cnf(c_0_129, negated_conjecture, (k7_relat_1(esk4_0,esk2_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_83])])).
% 3.04/3.22  cnf(c_0_130, negated_conjecture, (k2_relat_1(esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_119]), c_0_120]), c_0_83])])).
% 3.04/3.22  cnf(c_0_131, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))))=X1|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_105])])).
% 3.04/3.22  cnf(c_0_132, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_40]), c_0_51]), c_0_41]), c_0_42]), c_0_43])]), c_0_124])).
% 3.04/3.22  cnf(c_0_133, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),k5_relat_1(esk3_0,esk4_0))=k2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_70]), c_0_125]), c_0_62])])).
% 3.04/3.22  cnf(c_0_134, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|X3=k1_xboole_0|k9_relat_1(X1,X2)!=X3|~v1_funct_2(X1,X2,X3)|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 3.04/3.22  cnf(c_0_135, negated_conjecture, (k9_relat_1(esk4_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130]), c_0_83])])).
% 3.04/3.22  cnf(c_0_136, negated_conjecture, (k5_relat_1(k5_relat_1(esk3_0,esk4_0),k2_funct_1(esk4_0))=k2_funct_1(esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_70]), c_0_125]), c_0_62])]), c_0_132]), c_0_125]), c_0_133])).
% 3.04/3.22  cnf(c_0_137, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k5_relat_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_41]), c_0_125]), c_0_135]), c_0_82]), c_0_42]), c_0_43])]), c_0_124])).
% 3.04/3.22  cnf(c_0_138, negated_conjecture, (k5_relat_1(esk3_0,k5_relat_1(esk3_0,esk4_0))=esk3_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_68]), c_0_59])]), c_0_125])).
% 3.04/3.22  cnf(c_0_139, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_136]), c_0_137]), c_0_138]), c_0_62]), c_0_83]), c_0_59])])).
% 3.04/3.22  cnf(c_0_140, negated_conjecture, (k2_funct_1(esk3_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_139]), c_0_82]), c_0_42]), c_0_83])])).
% 3.04/3.22  cnf(c_0_141, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_78, c_0_140])).
% 3.04/3.22  cnf(c_0_142, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_110]), c_0_43])]), ['proof']).
% 3.04/3.22  # SZS output end CNFRefutation
% 3.04/3.22  # Proof object total steps             : 143
% 3.04/3.22  # Proof object clause steps            : 92
% 3.04/3.22  # Proof object formula steps           : 51
% 3.04/3.22  # Proof object conjectures             : 52
% 3.04/3.22  # Proof object clause conjectures      : 49
% 3.04/3.22  # Proof object formula conjectures     : 3
% 3.04/3.22  # Proof object initial clauses used    : 40
% 3.04/3.22  # Proof object initial formulas used   : 25
% 3.04/3.22  # Proof object generating inferences   : 45
% 3.04/3.22  # Proof object simplifying inferences  : 126
% 3.04/3.22  # Training examples: 0 positive, 0 negative
% 3.04/3.22  # Parsed axioms                        : 37
% 3.04/3.22  # Removed by relevancy pruning/SinE    : 0
% 3.04/3.22  # Initial clauses                      : 69
% 3.04/3.22  # Removed in clause preprocessing      : 2
% 3.04/3.22  # Initial clauses in saturation        : 67
% 3.04/3.22  # Processed clauses                    : 2515
% 3.04/3.22  # ...of these trivial                  : 145
% 3.04/3.22  # ...subsumed                          : 1152
% 3.04/3.22  # ...remaining for further processing  : 1218
% 3.04/3.22  # Other redundant clauses eliminated   : 8
% 3.04/3.22  # Clauses deleted for lack of memory   : 0
% 3.04/3.22  # Backward-subsumed                    : 13
% 3.04/3.22  # Backward-rewritten                   : 288
% 3.04/3.22  # Generated clauses                    : 129015
% 3.04/3.22  # ...of the previous two non-trivial   : 127412
% 3.04/3.22  # Contextual simplify-reflections      : 279
% 3.04/3.22  # Paramodulations                      : 129003
% 3.04/3.22  # Factorizations                       : 0
% 3.04/3.22  # Equation resolutions                 : 12
% 3.04/3.22  # Propositional unsat checks           : 0
% 3.04/3.22  #    Propositional check models        : 0
% 3.04/3.22  #    Propositional check unsatisfiable : 0
% 3.04/3.22  #    Propositional clauses             : 0
% 3.04/3.22  #    Propositional clauses after purity: 0
% 3.04/3.22  #    Propositional unsat core size     : 0
% 3.04/3.22  #    Propositional preprocessing time  : 0.000
% 3.04/3.22  #    Propositional encoding time       : 0.000
% 3.04/3.22  #    Propositional solver time         : 0.000
% 3.04/3.22  #    Success case prop preproc time    : 0.000
% 3.04/3.22  #    Success case prop encoding time   : 0.000
% 3.04/3.22  #    Success case prop solver time     : 0.000
% 3.04/3.22  # Current number of processed clauses  : 915
% 3.04/3.22  #    Positive orientable unit clauses  : 120
% 3.04/3.22  #    Positive unorientable unit clauses: 0
% 3.04/3.22  #    Negative unit clauses             : 3
% 3.04/3.22  #    Non-unit-clauses                  : 792
% 3.04/3.22  # Current number of unprocessed clauses: 124867
% 3.04/3.22  # ...number of literals in the above   : 1050125
% 3.04/3.22  # Current number of archived formulas  : 0
% 3.04/3.22  # Current number of archived clauses   : 302
% 3.04/3.22  # Clause-clause subsumption calls (NU) : 203577
% 3.04/3.22  # Rec. Clause-clause subsumption calls : 20606
% 3.04/3.22  # Non-unit clause-clause subsumptions  : 768
% 3.04/3.22  # Unit Clause-clause subsumption calls : 1706
% 3.04/3.22  # Rewrite failures with RHS unbound    : 0
% 3.04/3.22  # BW rewrite match attempts            : 508
% 3.04/3.22  # BW rewrite match successes           : 34
% 3.04/3.22  # Condensation attempts                : 0
% 3.04/3.22  # Condensation successes               : 0
% 3.04/3.22  # Termbank termtop insertions          : 7320025
% 3.04/3.23  
% 3.04/3.23  # -------------------------------------------------
% 3.04/3.23  # User time                : 2.795 s
% 3.04/3.23  # System time              : 0.085 s
% 3.04/3.23  # Total time               : 2.880 s
% 3.04/3.23  # Maximum resident set size: 1628 pages
%------------------------------------------------------------------------------
