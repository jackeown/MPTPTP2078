%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  113 (2238 expanded)
%              Number of clauses        :   74 ( 838 expanded)
%              Number of leaves         :   20 ( 545 expanded)
%              Depth                    :   16
%              Number of atoms          :  441 (13430 expanded)
%              Number of equality atoms :   96 (1005 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
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

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t28_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( ( k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X4,X5)) = X3
              & v2_funct_1(X5) )
           => ( X3 = k1_xboole_0
              | k2_relset_1(X1,X2,X4) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,X52,X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X53,X52)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))
      | k2_relset_1(X52,X53,X54) != X53
      | ~ r2_relset_1(X52,X52,k1_partfun1(X52,X53,X53,X52,X54,X55),k6_partfun1(X52))
      | ~ v2_funct_1(X54)
      | X52 = k1_xboole_0
      | X53 = k1_xboole_0
      | X55 = k2_funct_1(X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).

fof(c_0_22,plain,(
    ! [X38] : k6_partfun1(X38) = k6_relat_1(X38) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_23,plain,(
    ! [X48,X49,X50,X51] :
      ( ( v2_funct_1(X50)
        | ~ r2_relset_1(X48,X48,k1_partfun1(X48,X49,X49,X48,X50,X51),k6_partfun1(X48))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48)))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v2_funct_2(X51,X48)
        | ~ r2_relset_1(X48,X48,k1_partfun1(X48,X49,X49,X48,X50,X51),k6_partfun1(X48))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48)))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).

fof(c_0_24,plain,(
    ! [X35] :
      ( v1_partfun1(k6_partfun1(X35),X35)
      & m1_subset_1(k6_partfun1(X35),k1_zfmisc_1(k2_zfmisc_1(X35,X35))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( v1_funct_1(k1_partfun1(X27,X28,X29,X30,X31,X32))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( m1_subset_1(k1_partfun1(X27,X28,X29,X30,X31,X32),k1_zfmisc_1(k2_zfmisc_1(X27,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_26,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_27,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v2_funct_1(X1)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X36,X37] :
      ( ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,X36,X36)
      | ~ v3_funct_2(X37,X36,X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X36)))
      | k2_funct_2(X36,X37) = k2_funct_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_31,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r2_relset_1(X20,X21,X22,X23)
        | X22 = X23
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X22 != X23
        | r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
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
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_41,plain,(
    ! [X43,X44,X45,X46,X47] :
      ( ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,X43,X44)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,X44,X45)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k2_relset_1(X43,X45,k1_partfun1(X43,X44,X44,X45,X46,X47)) != X45
      | ~ v2_funct_1(X47)
      | X45 = k1_xboole_0
      | k2_relset_1(X43,X44,X46) = X44 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_funct_2])])])).

cnf(c_0_42,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk1_0,esk1_0,X3,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_46,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k2_relset_1(X17,X18,X19) = k2_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_47,plain,(
    ! [X10] :
      ( k1_relat_1(k6_relat_1(X10)) = X10
      & k2_relat_1(k6_relat_1(X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_48,plain,(
    ! [X24,X25,X26] :
      ( ( v1_funct_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v3_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v2_funct_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v3_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v2_funct_2(X26,X25)
        | ~ v1_funct_1(X26)
        | ~ v3_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

cnf(c_0_49,plain,
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

cnf(c_0_50,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( k2_funct_2(X1,esk2_0) = k2_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,X1,X1)
    | ~ v3_funct_2(esk2_0,X1,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,plain,
    ( X5 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | k2_relset_1(X2,X5,k1_partfun1(X2,X3,X3,X5,X1,X4)) != X5
    | ~ v2_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_40])])).

cnf(c_0_58,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( v3_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( k2_funct_1(esk2_0) = esk3_0
    | esk1_0 = k1_xboole_0
    | k2_relset_1(esk1_0,esk1_0,esk2_0) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_35]),c_0_40]),c_0_34]),c_0_45])])).

cnf(c_0_63,negated_conjecture,
    ( k2_funct_1(esk2_0) = k2_funct_2(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_45]),c_0_52]),c_0_54])])).

cnf(c_0_64,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    | X1 = k1_xboole_0
    | k2_relset_1(esk1_0,X1,k1_partfun1(esk1_0,esk1_0,esk1_0,X1,esk2_0,X2)) != X1
    | ~ v1_funct_2(X2,esk1_0,X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_52]),c_0_40])])).

cnf(c_0_65,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_50])])).

cnf(c_0_66,plain,
    ( k2_relset_1(X1,X1,k6_relat_1(X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_43]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_35]),c_0_34])])).

cnf(c_0_68,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_69,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,X39,X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X40,X39)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X39)))
      | ~ r2_relset_1(X40,X40,k1_partfun1(X40,X39,X39,X40,X42,X41),k6_partfun1(X40))
      | k2_relset_1(X39,X40,X41) = X40 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

cnf(c_0_70,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = esk3_0
    | esk1_0 = k1_xboole_0
    | k2_relset_1(esk1_0,esk1_0,esk2_0) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_51]),c_0_67]),c_0_35]),c_0_34])])).

cnf(c_0_72,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_68])).

fof(c_0_73,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_74,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_75,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_xboole_0(X14)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_xboole_0(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_77,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = esk3_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_34])).

fof(c_0_79,plain,(
    ! [X9] :
      ( ( k1_relat_1(X9) != k1_xboole_0
        | X9 = k1_xboole_0
        | ~ v1_relat_1(X9) )
      & ( k2_relat_1(X9) != k1_xboole_0
        | X9 = k1_xboole_0
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_80,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_28])).

fof(c_0_82,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | X7 = X8
      | ~ v1_xboole_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_85,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k2_relat_1(esk3_0) = k2_relset_1(esk1_0,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_34])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_34])).

cnf(c_0_89,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,X1) = esk1_0
    | ~ v1_funct_2(X1,esk1_0,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,X1),k6_relat_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_45]),c_0_52]),c_0_40])])).

cnf(c_0_90,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_43])).

fof(c_0_91,plain,(
    ! [X33,X34] :
      ( ( v1_funct_1(k2_funct_2(X33,X34))
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X33,X33)
        | ~ v3_funct_2(X34,X33,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33))) )
      & ( v1_funct_2(k2_funct_2(X33,X34),X33,X33)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X33,X33)
        | ~ v3_funct_2(X34,X33,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33))) )
      & ( v3_funct_2(k2_funct_2(X33,X34),X33,X33)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X33,X33)
        | ~ v3_funct_2(X34,X33,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33))) )
      & ( m1_subset_1(k2_funct_2(X33,X34),k1_zfmisc_1(k2_zfmisc_1(X33,X33)))
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X33,X33)
        | ~ v3_funct_2(X34,X33,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_93,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_85]),c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k2_relset_1(esk1_0,esk1_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_96,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_51]),c_0_35]),c_0_65]),c_0_90]),c_0_34])])).

cnf(c_0_97,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_84])).

cnf(c_0_99,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_45]),c_0_52]),c_0_54]),c_0_40])])).

cnf(c_0_102,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_85])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_85]),c_0_85]),c_0_85]),c_0_102])).

cnf(c_0_105,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_85]),c_0_85]),c_0_85]),c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( v1_xboole_0(k2_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_104])).

cnf(c_0_108,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_106,c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k2_funct_2(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_107])).

cnf(c_0_111,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_111])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EI
% 0.19/0.41  # and selection function SelectDivPreferIntoLits.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t87_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 0.19/0.41  fof(t36_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.19/0.42  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.42  fof(t29_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 0.19/0.42  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.19/0.42  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.42  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.19/0.42  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.42  fof(t28_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X4,X5))=X3&v2_funct_1(X5))=>(X3=k1_xboole_0|k2_relset_1(X1,X2,X4)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 0.19/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.42  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.42  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.19/0.42  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 0.19/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.42  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.19/0.42  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.42  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.42  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.19/0.42  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.42  fof(c_0_20, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)))))), inference(assume_negation,[status(cth)],[t87_funct_2])).
% 0.19/0.42  fof(c_0_21, plain, ![X52, X53, X54, X55]:(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))|(k2_relset_1(X52,X53,X54)!=X53|~r2_relset_1(X52,X52,k1_partfun1(X52,X53,X53,X52,X54,X55),k6_partfun1(X52))|~v2_funct_1(X54)|(X52=k1_xboole_0|X53=k1_xboole_0|X55=k2_funct_1(X54))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).
% 0.19/0.42  fof(c_0_22, plain, ![X38]:k6_partfun1(X38)=k6_relat_1(X38), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.42  fof(c_0_23, plain, ![X48, X49, X50, X51]:((v2_funct_1(X50)|~r2_relset_1(X48,X48,k1_partfun1(X48,X49,X49,X48,X50,X51),k6_partfun1(X48))|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48))))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&(v2_funct_2(X51,X48)|~r2_relset_1(X48,X48,k1_partfun1(X48,X49,X49,X48,X50,X51),k6_partfun1(X48))|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48))))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).
% 0.19/0.42  fof(c_0_24, plain, ![X35]:(v1_partfun1(k6_partfun1(X35),X35)&m1_subset_1(k6_partfun1(X35),k1_zfmisc_1(k2_zfmisc_1(X35,X35)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.19/0.42  fof(c_0_25, plain, ![X27, X28, X29, X30, X31, X32]:((v1_funct_1(k1_partfun1(X27,X28,X29,X30,X31,X32))|(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(m1_subset_1(k1_partfun1(X27,X28,X29,X30,X31,X32),k1_zfmisc_1(k2_zfmisc_1(X27,X30)))|(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.42  fof(c_0_26, negated_conjecture, ((((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&v3_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&v3_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0))&~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.42  cnf(c_0_27, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X4=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|k2_relset_1(X2,X3,X1)!=X3|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_28, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_29, plain, (v2_funct_1(X1)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  fof(c_0_30, plain, ![X36, X37]:(~v1_funct_1(X37)|~v1_funct_2(X37,X36,X36)|~v3_funct_2(X37,X36,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X36)))|k2_funct_2(X36,X37)=k2_funct_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.19/0.42  fof(c_0_31, plain, ![X20, X21, X22, X23]:((~r2_relset_1(X20,X21,X22,X23)|X22=X23|(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(X22!=X23|r2_relset_1(X20,X21,X22,X23)|(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.42  cnf(c_0_32, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_33, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_36, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.42  cnf(c_0_37, plain, (v2_funct_1(X1)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_39, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  fof(c_0_41, plain, ![X43, X44, X45, X46, X47]:(~v1_funct_1(X46)|~v1_funct_2(X46,X43,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|(k2_relset_1(X43,X45,k1_partfun1(X43,X44,X44,X45,X46,X47))!=X45|~v2_funct_1(X47)|(X45=k1_xboole_0|k2_relset_1(X43,X44,X46)=X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_funct_2])])])).
% 0.19/0.42  cnf(c_0_42, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_43, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_32, c_0_28])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk1_0,esk1_0,X3,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  fof(c_0_46, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|k2_relset_1(X17,X18,X19)=k2_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.42  fof(c_0_47, plain, ![X10]:(k1_relat_1(k6_relat_1(X10))=X10&k2_relat_1(k6_relat_1(X10))=X10), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.42  fof(c_0_48, plain, ![X24, X25, X26]:(((v1_funct_1(X26)|(~v1_funct_1(X26)|~v3_funct_2(X26,X24,X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(v2_funct_1(X26)|(~v1_funct_1(X26)|~v3_funct_2(X26,X24,X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&(v2_funct_2(X26,X25)|(~v1_funct_1(X26)|~v3_funct_2(X26,X24,X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.19/0.42  cnf(c_0_49, plain, (X1=k2_funct_1(X2)|X3=k1_xboole_0|X4=k1_xboole_0|k2_relset_1(X3,X4,X2)!=X4|~v1_funct_2(X1,X4,X3)|~v1_funct_2(X2,X3,X4)|~v1_funct_1(X1)|~v1_funct_1(X2)|~r2_relset_1(X3,X3,k1_partfun1(X3,X4,X4,X3,X2,X1),k6_relat_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(csr,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_38, c_0_28])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (k2_funct_2(X1,esk2_0)=k2_funct_1(esk2_0)|~v1_funct_2(esk2_0,X1,X1)|~v3_funct_2(esk2_0,X1,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (v3_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_55, plain, (X5=k1_xboole_0|k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X5)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))|k2_relset_1(X2,X5,k1_partfun1(X2,X3,X3,X5,X1,X4))!=X5|~v2_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  cnf(c_0_56, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_40])])).
% 0.19/0.42  cnf(c_0_58, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_59, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_60, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (v3_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_62, negated_conjecture, (k2_funct_1(esk2_0)=esk3_0|esk1_0=k1_xboole_0|k2_relset_1(esk1_0,esk1_0,esk2_0)!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_35]), c_0_40]), c_0_34]), c_0_45])])).
% 0.19/0.42  cnf(c_0_63, negated_conjecture, (k2_funct_1(esk2_0)=k2_funct_2(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_45]), c_0_52]), c_0_54])])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0|X1=k1_xboole_0|k2_relset_1(esk1_0,X1,k1_partfun1(esk1_0,esk1_0,esk1_0,X1,esk2_0,X2))!=X1|~v1_funct_2(X2,esk1_0,X1)|~v2_funct_1(X2)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_52]), c_0_40])])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_50])])).
% 0.19/0.42  cnf(c_0_66, plain, (k2_relset_1(X1,X1,k6_relat_1(X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_43]), c_0_59])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_35]), c_0_34])])).
% 0.19/0.42  cnf(c_0_68, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  fof(c_0_69, plain, ![X39, X40, X41, X42]:(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X39)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X39)))|(~r2_relset_1(X40,X40,k1_partfun1(X40,X39,X39,X40,X42,X41),k6_partfun1(X40))|k2_relset_1(X39,X40,X41)=X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=esk3_0|esk1_0=k1_xboole_0|k2_relset_1(esk1_0,esk1_0,esk2_0)!=esk1_0), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0|esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_51]), c_0_67]), c_0_35]), c_0_34])])).
% 0.19/0.42  cnf(c_0_72, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.42  fof(c_0_73, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.42  cnf(c_0_74, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.42  fof(c_0_75, plain, ![X14, X15, X16]:(~v1_xboole_0(X14)|(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_xboole_0(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_2(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=esk3_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_34])).
% 0.19/0.42  fof(c_0_79, plain, ![X9]:((k1_relat_1(X9)!=k1_xboole_0|X9=k1_xboole_0|~v1_relat_1(X9))&(k2_relat_1(X9)!=k1_xboole_0|X9=k1_xboole_0|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.42  cnf(c_0_80, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.42  cnf(c_0_81, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_74, c_0_28])).
% 0.19/0.42  fof(c_0_82, plain, ![X7, X8]:(~v1_xboole_0(X7)|X7=X8|~v1_xboole_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.42  cnf(c_0_83, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.42  cnf(c_0_84, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.42  cnf(c_0_85, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.19/0.42  cnf(c_0_86, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.42  cnf(c_0_87, negated_conjecture, (k2_relat_1(esk3_0)=k2_relset_1(esk1_0,esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_34])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_80, c_0_34])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,X1)=esk1_0|~v1_funct_2(X1,esk1_0,esk1_0)|~v1_funct_1(X1)|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,X1),k6_relat_1(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_45]), c_0_52]), c_0_40])])).
% 0.19/0.42  cnf(c_0_90, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_43])).
% 0.19/0.42  fof(c_0_91, plain, ![X33, X34]:((((v1_funct_1(k2_funct_2(X33,X34))|(~v1_funct_1(X34)|~v1_funct_2(X34,X33,X33)|~v3_funct_2(X34,X33,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33)))))&(v1_funct_2(k2_funct_2(X33,X34),X33,X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,X33,X33)|~v3_funct_2(X34,X33,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33))))))&(v3_funct_2(k2_funct_2(X33,X34),X33,X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,X33,X33)|~v3_funct_2(X34,X33,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33))))))&(m1_subset_1(k2_funct_2(X33,X34),k1_zfmisc_1(k2_zfmisc_1(X33,X33)))|(~v1_funct_1(X34)|~v1_funct_2(X34,X33,X33)|~v3_funct_2(X34,X33,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.19/0.42  cnf(c_0_92, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.42  cnf(c_0_93, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_85]), c_0_85])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (esk3_0=k1_xboole_0|k2_relset_1(esk1_0,esk1_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.19/0.42  cnf(c_0_96, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_51]), c_0_35]), c_0_65]), c_0_90]), c_0_34])])).
% 0.19/0.42  cnf(c_0_97, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.42  cnf(c_0_98, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_92, c_0_84])).
% 0.19/0.42  cnf(c_0_99, negated_conjecture, (v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.19/0.42  cnf(c_0_100, negated_conjecture, (esk3_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 0.19/0.42  cnf(c_0_101, negated_conjecture, (m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_45]), c_0_52]), c_0_54]), c_0_40])])).
% 0.19/0.42  cnf(c_0_102, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.42  cnf(c_0_103, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_85])])).
% 0.19/0.42  cnf(c_0_104, negated_conjecture, (m1_subset_1(k2_funct_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_85]), c_0_85]), c_0_85]), c_0_102])).
% 0.19/0.42  cnf(c_0_105, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.42  cnf(c_0_106, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_85]), c_0_85]), c_0_85]), c_0_103])).
% 0.19/0.42  cnf(c_0_107, negated_conjecture, (v1_xboole_0(k2_funct_2(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_93, c_0_104])).
% 0.19/0.42  cnf(c_0_108, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_43, c_0_105])).
% 0.19/0.42  cnf(c_0_109, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[c_0_106, c_0_102])).
% 0.19/0.42  cnf(c_0_110, negated_conjecture, (k2_funct_2(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_107])).
% 0.19/0.42  cnf(c_0_111, plain, (r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_108])).
% 0.19/0.42  cnf(c_0_112, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_111])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 113
% 0.19/0.42  # Proof object clause steps            : 74
% 0.19/0.42  # Proof object formula steps           : 39
% 0.19/0.42  # Proof object conjectures             : 44
% 0.19/0.42  # Proof object clause conjectures      : 41
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 30
% 0.19/0.42  # Proof object initial formulas used   : 20
% 0.19/0.42  # Proof object generating inferences   : 29
% 0.19/0.42  # Proof object simplifying inferences  : 70
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 20
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 40
% 0.19/0.42  # Removed in clause preprocessing      : 2
% 0.19/0.42  # Initial clauses in saturation        : 38
% 0.19/0.42  # Processed clauses                    : 469
% 0.19/0.42  # ...of these trivial                  : 16
% 0.19/0.42  # ...subsumed                          : 17
% 0.19/0.42  # ...remaining for further processing  : 436
% 0.19/0.42  # Other redundant clauses eliminated   : 3
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 1
% 0.19/0.42  # Backward-rewritten                   : 335
% 0.19/0.42  # Generated clauses                    : 1393
% 0.19/0.42  # ...of the previous two non-trivial   : 1545
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 1390
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 3
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 61
% 0.19/0.42  #    Positive orientable unit clauses  : 27
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 0
% 0.19/0.42  #    Non-unit-clauses                  : 34
% 0.19/0.42  # Current number of unprocessed clauses: 910
% 0.19/0.42  # ...number of literals in the above   : 2903
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 375
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 2252
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 1040
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 19
% 0.19/0.42  # Unit Clause-clause subsumption calls : 163
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 2104
% 0.19/0.42  # BW rewrite match successes           : 14
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 60112
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.079 s
% 0.19/0.42  # System time              : 0.004 s
% 0.19/0.42  # Total time               : 0.083 s
% 0.19/0.42  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
