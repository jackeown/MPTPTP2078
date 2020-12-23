%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:17 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  179 (2164 expanded)
%              Number of clauses        :  120 ( 858 expanded)
%              Number of leaves         :   29 ( 564 expanded)
%              Depth                    :   20
%              Number of atoms          :  472 (9765 expanded)
%              Number of equality atoms :  134 (2680 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t164_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(c_0_29,negated_conjecture,(
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

fof(c_0_30,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_31,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_32,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_34,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | k7_relat_1(X30,X29) = k5_relat_1(k6_relat_1(X29),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_35,plain,(
    ! [X49] : m1_subset_1(k6_relat_1(X49),k1_zfmisc_1(k2_zfmisc_1(X49,X49))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_36,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X39,X40,X41] :
      ( ( v4_relat_1(X41,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v5_relat_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_40,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k9_relat_1(X14,k1_relat_1(X14)) = k2_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_41,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k4_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_42,plain,(
    ! [X63] :
      ( ( v1_funct_1(X63)
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) )
      & ( v1_funct_2(X63,k1_relat_1(X63),k2_relat_1(X63))
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) )
      & ( m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X63),k2_relat_1(X63))))
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_43,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | r1_tarski(k2_relat_1(k5_relat_1(X19,X20)),k2_relat_1(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_44,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k4_relat_1(k5_relat_1(X21,X22)) = k5_relat_1(k4_relat_1(X22),k4_relat_1(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

fof(c_0_49,plain,(
    ! [X27] : k4_relat_1(k6_relat_1(X27)) = k6_relat_1(X27) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_50,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v4_relat_1(X18,X17)
      | X18 = k7_relat_1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_51,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X37] :
      ( ( k2_relat_1(X37) = k1_relat_1(k2_funct_1(X37))
        | ~ v2_funct_1(X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( k1_relat_1(X37) = k2_relat_1(k2_funct_1(X37))
        | ~ v2_funct_1(X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_53,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ v2_funct_1(X31)
      | k2_funct_1(X31) = k4_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_54,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_57,plain,(
    ! [X32] :
      ( ( v1_relat_1(k2_funct_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_1(k2_funct_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_60,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_46]),c_0_38])])).

fof(c_0_61,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ v2_funct_1(X34)
      | k10_relat_1(X34,X33) = k9_relat_1(k2_funct_1(X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

cnf(c_0_62,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k5_relat_1(k6_relat_1(X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_64,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_37])).

cnf(c_0_67,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,plain,
    ( k2_relat_1(k4_relat_1(X1)) = k9_relat_1(k4_relat_1(X1),k1_relat_1(k4_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_70,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_71,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_56])).

cnf(c_0_72,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_74,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,negated_conjecture,
    ( k4_relat_1(k7_relat_1(esk3_0,X1)) = k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_48]),c_0_60])])).

cnf(c_0_76,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_48])])).

cnf(c_0_77,plain,
    ( k2_relat_1(k4_relat_1(X1)) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk3_0)) = k9_relat_1(k4_relat_1(esk3_0),k1_relat_1(k4_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_81,plain,
    ( k1_relat_1(k4_relat_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( k2_relat_1(esk3_0) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_83,plain,
    ( v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_84,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_85,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(X1)))
    | ~ v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(esk1_0)) = k4_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_88,negated_conjecture,
    ( k9_relat_1(k4_relat_1(esk3_0),k1_relat_1(k4_relat_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_48]),c_0_78]),c_0_79]),c_0_80])])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_48]),c_0_82]),c_0_79]),c_0_80])])).

fof(c_0_90,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_91,plain,
    ( v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_92,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ r1_tarski(X35,k1_relat_1(X36))
      | ~ v2_funct_1(X36)
      | k10_relat_1(X36,k9_relat_1(X36,X35)) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).

cnf(c_0_93,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k2_relat_1(k4_relat_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_68])).

cnf(c_0_94,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_76]),c_0_87]),c_0_48])])).

cnf(c_0_95,negated_conjecture,
    ( k9_relat_1(k4_relat_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,plain,
    ( v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_70])).

cnf(c_0_98,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_78]),c_0_89]),c_0_95]),c_0_79]),c_0_80]),c_0_48])])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_82]),c_0_79]),c_0_80]),c_0_48])])).

cnf(c_0_102,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))) = k10_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_79]),c_0_80]),c_0_48])])).

cnf(c_0_103,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_100])).

fof(c_0_104,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k2_relset_1(X42,X43,X44) = k2_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k2_funct_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))) = k10_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_102]),c_0_79]),c_0_80]),c_0_48])])).

cnf(c_0_107,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_48]),c_0_79]),c_0_80])])).

fof(c_0_108,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_relat_1(X25)
      | k5_relat_1(k5_relat_1(X23,X24),X25) = k5_relat_1(X23,k5_relat_1(X24,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_109,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_111,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(X1),X2)) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_72])).

cnf(c_0_112,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_72]),c_0_80]),c_0_48])])).

cnf(c_0_113,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

fof(c_0_115,plain,(
    ! [X62] : k6_partfun1(X62) = k6_relat_1(X62) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_116,plain,(
    ! [X56,X57,X58,X59,X60,X61] :
      ( ~ v1_funct_1(X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | ~ v1_funct_1(X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | k1_partfun1(X56,X57,X58,X59,X60,X61) = k5_relat_1(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_118,negated_conjecture,
    ( esk2_0 = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_37]),c_0_110]),c_0_82])).

fof(c_0_119,plain,(
    ! [X38] :
      ( ( k5_relat_1(X38,k2_funct_1(X38)) = k6_relat_1(k1_relat_1(X38))
        | ~ v2_funct_1(X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( k5_relat_1(k2_funct_1(X38),X38) = k6_relat_1(k2_relat_1(X38))
        | ~ v2_funct_1(X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_120,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113]),c_0_80]),c_0_48])])).

cnf(c_0_121,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),X2) = k5_relat_1(X1,k5_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_48])).

cnf(c_0_122,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_123,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_124,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0))) ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_127,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_120])).

cnf(c_0_129,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),k6_relat_1(X2)) = k5_relat_1(X1,k5_relat_1(esk3_0,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_60])).

cnf(c_0_130,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

fof(c_0_131,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | k5_relat_1(X28,k6_relat_1(k2_relat_1(X28))) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_132,plain,(
    ! [X26] :
      ( k1_relat_1(k6_relat_1(X26)) = X26
      & k2_relat_1(k6_relat_1(X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_133,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ r2_relset_1(X45,X46,X47,X48)
        | X47 = X48
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X47 != X48
        | r2_relset_1(X45,X46,X47,X48)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_134,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_135,negated_conjecture,
    ( k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126])])).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_118])).

fof(c_0_137,plain,(
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

cnf(c_0_138,plain,
    ( k5_relat_1(X1,k4_relat_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_68])).

cnf(c_0_139,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_84]),c_0_80]),c_0_48])])).

cnf(c_0_140,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k6_relat_1(X1))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_82]),c_0_79]),c_0_80]),c_0_48])])).

cnf(c_0_141,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_142,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_132])).

cnf(c_0_143,plain,
    ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_60]),c_0_64])).

cnf(c_0_144,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_133])).

cnf(c_0_145,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_118]),c_0_118])).

cnf(c_0_146,negated_conjecture,
    ( k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_80])])).

cnf(c_0_147,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_148,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_117])).

cnf(c_0_149,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_117]),c_0_38])])).

cnf(c_0_150,negated_conjecture,
    ( k5_relat_1(esk3_0,k4_relat_1(esk3_0)) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_48]),c_0_79]),c_0_80])])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_72]),c_0_80]),c_0_48])])).

cnf(c_0_152,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_72]),c_0_80]),c_0_48])])).

cnf(c_0_153,negated_conjecture,
    ( k5_relat_1(esk3_0,k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_48]),c_0_82])).

cnf(c_0_154,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_60]),c_0_142])).

cnf(c_0_155,negated_conjecture,
    ( k4_relat_1(k5_relat_1(esk3_0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_48])).

cnf(c_0_156,plain,
    ( k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1)))) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_141,c_0_72])).

cnf(c_0_157,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_144,c_0_46])).

cnf(c_0_158,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_159,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_125]),c_0_126])])).

cnf(c_0_160,plain,
    ( k5_relat_1(k4_relat_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_68])).

cnf(c_0_161,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_148]),c_0_149])])).

cnf(c_0_162,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k5_relat_1(k6_relat_1(X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_149])).

cnf(c_0_163,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),k4_relat_1(esk3_0)) = k5_relat_1(X1,k6_relat_1(k1_relat_1(esk3_0)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_94]),c_0_150])).

cnf(c_0_164,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_151]),c_0_38])])).

cnf(c_0_165,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154])).

cnf(c_0_166,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k4_relat_1(esk3_0)) = k4_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_153])).

cnf(c_0_167,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0))) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_120]),c_0_80]),c_0_48])])).

cnf(c_0_168,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_169,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_136]),c_0_146]),c_0_80])])).

cnf(c_0_170,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0) = k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_149])).

cnf(c_0_171,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk3_0),esk3_0) = k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_48]),c_0_82]),c_0_79]),c_0_80])])).

cnf(c_0_172,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_161,c_0_118]),c_0_162])).

cnf(c_0_173,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_174,negated_conjecture,
    ( k2_funct_1(esk3_0) = k4_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_165]),c_0_166]),c_0_167])).

cnf(c_0_175,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_168,c_0_169])])).

cnf(c_0_176,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_172]),c_0_94])])).

cnf(c_0_177,negated_conjecture,
    ( esk4_0 != k4_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_173,c_0_174])).

cnf(c_0_178,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_175]),c_0_176]),c_0_177]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:28:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 7.72/7.90  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 7.72/7.90  # and selection function SelectNewComplexAHP.
% 7.72/7.90  #
% 7.72/7.90  # Preprocessing time       : 0.029 s
% 7.72/7.90  
% 7.72/7.90  # Proof found!
% 7.72/7.90  # SZS status Theorem
% 7.72/7.90  # SZS output start CNFRefutation
% 7.72/7.90  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.72/7.90  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.72/7.90  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.72/7.90  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.72/7.90  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 7.72/7.90  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.72/7.90  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.72/7.90  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 7.72/7.90  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.72/7.90  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.72/7.90  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 7.72/7.90  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 7.72/7.90  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 7.72/7.90  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.72/7.90  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.72/7.90  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 7.72/7.90  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.72/7.90  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 7.72/7.90  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.72/7.90  fof(t164_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 7.72/7.90  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.72/7.90  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.72/7.90  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.72/7.90  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.72/7.90  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.72/7.90  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 7.72/7.90  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.72/7.90  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.72/7.90  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.72/7.90  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 7.72/7.90  fof(c_0_30, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 7.72/7.90  fof(c_0_31, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 7.72/7.90  fof(c_0_32, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 7.72/7.90  fof(c_0_33, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 7.72/7.90  fof(c_0_34, plain, ![X29, X30]:(~v1_relat_1(X30)|k7_relat_1(X30,X29)=k5_relat_1(k6_relat_1(X29),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 7.72/7.90  fof(c_0_35, plain, ![X49]:m1_subset_1(k6_relat_1(X49),k1_zfmisc_1(k2_zfmisc_1(X49,X49))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 7.72/7.90  cnf(c_0_36, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.72/7.90  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.90  cnf(c_0_38, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 7.72/7.90  fof(c_0_39, plain, ![X39, X40, X41]:((v4_relat_1(X41,X39)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(v5_relat_1(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 7.72/7.90  fof(c_0_40, plain, ![X14]:(~v1_relat_1(X14)|k9_relat_1(X14,k1_relat_1(X14))=k2_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 7.72/7.90  fof(c_0_41, plain, ![X11]:(~v1_relat_1(X11)|v1_relat_1(k4_relat_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 7.72/7.90  fof(c_0_42, plain, ![X63]:(((v1_funct_1(X63)|(~v1_relat_1(X63)|~v1_funct_1(X63)))&(v1_funct_2(X63,k1_relat_1(X63),k2_relat_1(X63))|(~v1_relat_1(X63)|~v1_funct_1(X63))))&(m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X63),k2_relat_1(X63))))|(~v1_relat_1(X63)|~v1_funct_1(X63)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 7.72/7.90  fof(c_0_43, plain, ![X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|r1_tarski(k2_relat_1(k5_relat_1(X19,X20)),k2_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 7.72/7.90  cnf(c_0_44, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 7.72/7.90  cnf(c_0_45, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.72/7.90  cnf(c_0_46, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 7.72/7.90  fof(c_0_47, plain, ![X21, X22]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|k4_relat_1(k5_relat_1(X21,X22))=k5_relat_1(k4_relat_1(X22),k4_relat_1(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 7.72/7.90  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 7.72/7.90  fof(c_0_49, plain, ![X27]:k4_relat_1(k6_relat_1(X27))=k6_relat_1(X27), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 7.72/7.90  fof(c_0_50, plain, ![X17, X18]:(~v1_relat_1(X18)|~v4_relat_1(X18,X17)|X18=k7_relat_1(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 7.72/7.90  cnf(c_0_51, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 7.72/7.90  fof(c_0_52, plain, ![X37]:((k2_relat_1(X37)=k1_relat_1(k2_funct_1(X37))|~v2_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(k1_relat_1(X37)=k2_relat_1(k2_funct_1(X37))|~v2_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 7.72/7.90  fof(c_0_53, plain, ![X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~v2_funct_1(X31)|k2_funct_1(X31)=k4_relat_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 7.72/7.90  cnf(c_0_54, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 7.72/7.90  cnf(c_0_55, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 7.72/7.90  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 7.72/7.90  fof(c_0_57, plain, ![X32]:((v1_relat_1(k2_funct_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(v1_funct_1(k2_funct_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 7.72/7.90  cnf(c_0_58, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 7.72/7.90  cnf(c_0_59, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k9_relat_1(X2,X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 7.72/7.90  cnf(c_0_60, plain, (v1_relat_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_46]), c_0_38])])).
% 7.72/7.90  fof(c_0_61, plain, ![X33, X34]:(~v1_relat_1(X34)|~v1_funct_1(X34)|(~v2_funct_1(X34)|k10_relat_1(X34,X33)=k9_relat_1(k2_funct_1(X34),X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 7.72/7.90  cnf(c_0_62, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 7.72/7.90  cnf(c_0_63, negated_conjecture, (k7_relat_1(esk3_0,X1)=k5_relat_1(k6_relat_1(X1),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_48])).
% 7.72/7.90  cnf(c_0_64, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 7.72/7.90  cnf(c_0_65, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 7.72/7.90  cnf(c_0_66, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_51, c_0_37])).
% 7.72/7.90  cnf(c_0_67, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 7.72/7.90  cnf(c_0_68, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 7.72/7.90  cnf(c_0_69, plain, (k2_relat_1(k4_relat_1(X1))=k9_relat_1(k4_relat_1(X1),k1_relat_1(k4_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 7.72/7.90  cnf(c_0_70, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 7.72/7.90  cnf(c_0_71, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_56])).
% 7.72/7.90  cnf(c_0_72, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 7.72/7.90  cnf(c_0_73, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 7.72/7.90  cnf(c_0_74, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 7.72/7.90  cnf(c_0_75, negated_conjecture, (k4_relat_1(k7_relat_1(esk3_0,X1))=k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_48]), c_0_60])])).
% 7.72/7.90  cnf(c_0_76, negated_conjecture, (k7_relat_1(esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_48])])).
% 7.72/7.90  cnf(c_0_77, plain, (k2_relat_1(k4_relat_1(X1))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 7.72/7.90  cnf(c_0_78, negated_conjecture, (k2_relat_1(k4_relat_1(esk3_0))=k9_relat_1(k4_relat_1(esk3_0),k1_relat_1(k4_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_69, c_0_48])).
% 7.72/7.90  cnf(c_0_79, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.90  cnf(c_0_80, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.90  cnf(c_0_81, plain, (k1_relat_1(k4_relat_1(X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_68])).
% 7.72/7.90  cnf(c_0_82, negated_conjecture, (k2_relat_1(esk3_0)=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 7.72/7.90  cnf(c_0_83, plain, (v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 7.72/7.90  cnf(c_0_84, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 7.72/7.90  cnf(c_0_85, plain, (r1_tarski(k10_relat_1(X1,X2),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 7.72/7.90  cnf(c_0_86, negated_conjecture, (v1_relat_1(k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(X1)))|~v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_55, c_0_75])).
% 7.72/7.90  cnf(c_0_87, negated_conjecture, (k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(esk1_0))=k4_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 7.72/7.90  cnf(c_0_88, negated_conjecture, (k9_relat_1(k4_relat_1(esk3_0),k1_relat_1(k4_relat_1(esk3_0)))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_48]), c_0_78]), c_0_79]), c_0_80])])).
% 7.72/7.90  cnf(c_0_89, negated_conjecture, (k1_relat_1(k4_relat_1(esk3_0))=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_48]), c_0_82]), c_0_79]), c_0_80])])).
% 7.72/7.90  fof(c_0_90, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.72/7.90  cnf(c_0_91, plain, (v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 7.72/7.90  fof(c_0_92, plain, ![X35, X36]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~r1_tarski(X35,k1_relat_1(X36))|~v2_funct_1(X36)|k10_relat_1(X36,k9_relat_1(X36,X35))=X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).
% 7.72/7.90  cnf(c_0_93, plain, (r1_tarski(k10_relat_1(X1,X2),k2_relat_1(k4_relat_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_68])).
% 7.72/7.90  cnf(c_0_94, negated_conjecture, (v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_76]), c_0_87]), c_0_48])])).
% 7.72/7.90  cnf(c_0_95, negated_conjecture, (k9_relat_1(k4_relat_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 7.72/7.90  cnf(c_0_96, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_90])).
% 7.72/7.90  cnf(c_0_97, plain, (v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_70])).
% 7.72/7.90  cnf(c_0_98, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 7.72/7.90  cnf(c_0_99, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_78]), c_0_89]), c_0_95]), c_0_79]), c_0_80]), c_0_48])])).
% 7.72/7.90  cnf(c_0_100, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_96])).
% 7.72/7.90  cnf(c_0_101, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_82]), c_0_79]), c_0_80]), c_0_48])])).
% 7.72/7.90  cnf(c_0_102, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))=k10_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_79]), c_0_80]), c_0_48])])).
% 7.72/7.90  cnf(c_0_103, plain, (k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_98, c_0_100])).
% 7.72/7.90  fof(c_0_104, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k2_relset_1(X42,X43,X44)=k2_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 7.72/7.90  cnf(c_0_105, negated_conjecture, (k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_101])).
% 7.72/7.90  cnf(c_0_106, negated_conjecture, (k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))=k10_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_102]), c_0_79]), c_0_80]), c_0_48])])).
% 7.72/7.90  cnf(c_0_107, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_48]), c_0_79]), c_0_80])])).
% 7.72/7.90  fof(c_0_108, plain, ![X23, X24, X25]:(~v1_relat_1(X23)|(~v1_relat_1(X24)|(~v1_relat_1(X25)|k5_relat_1(k5_relat_1(X23,X24),X25)=k5_relat_1(X23,k5_relat_1(X24,X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 7.72/7.90  cnf(c_0_109, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 7.72/7.90  cnf(c_0_110, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.90  cnf(c_0_111, plain, (k2_relat_1(k7_relat_1(k2_funct_1(X1),X2))=k9_relat_1(k2_funct_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_72])).
% 7.72/7.90  cnf(c_0_112, negated_conjecture, (k7_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_72]), c_0_80]), c_0_48])])).
% 7.72/7.90  cnf(c_0_113, negated_conjecture, (k9_relat_1(k2_funct_1(esk3_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 7.72/7.90  cnf(c_0_114, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 7.72/7.91  fof(c_0_115, plain, ![X62]:k6_partfun1(X62)=k6_relat_1(X62), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 7.72/7.91  fof(c_0_116, plain, ![X56, X57, X58, X59, X60, X61]:(~v1_funct_1(X60)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|k1_partfun1(X56,X57,X58,X59,X60,X61)=k5_relat_1(X60,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 7.72/7.91  cnf(c_0_117, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.91  cnf(c_0_118, negated_conjecture, (esk2_0=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_37]), c_0_110]), c_0_82])).
% 7.72/7.91  fof(c_0_119, plain, ![X38]:((k5_relat_1(X38,k2_funct_1(X38))=k6_relat_1(k1_relat_1(X38))|~v2_funct_1(X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(k5_relat_1(k2_funct_1(X38),X38)=k6_relat_1(k2_relat_1(X38))|~v2_funct_1(X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 7.72/7.91  cnf(c_0_120, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113]), c_0_80]), c_0_48])])).
% 7.72/7.91  cnf(c_0_121, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),X2)=k5_relat_1(X1,k5_relat_1(esk3_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_114, c_0_48])).
% 7.72/7.91  cnf(c_0_122, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.91  cnf(c_0_123, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 7.72/7.91  cnf(c_0_124, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 7.72/7.91  cnf(c_0_125, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0)))), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 7.72/7.91  cnf(c_0_126, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.91  cnf(c_0_127, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_119])).
% 7.72/7.91  cnf(c_0_128, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_120])).
% 7.72/7.91  cnf(c_0_129, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),k6_relat_1(X2))=k5_relat_1(X1,k5_relat_1(esk3_0,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_121, c_0_60])).
% 7.72/7.91  cnf(c_0_130, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_119])).
% 7.72/7.91  fof(c_0_131, plain, ![X28]:(~v1_relat_1(X28)|k5_relat_1(X28,k6_relat_1(k2_relat_1(X28)))=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 7.72/7.91  fof(c_0_132, plain, ![X26]:(k1_relat_1(k6_relat_1(X26))=X26&k2_relat_1(k6_relat_1(X26))=X26), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 7.72/7.91  fof(c_0_133, plain, ![X45, X46, X47, X48]:((~r2_relset_1(X45,X46,X47,X48)|X47=X48|(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&(X47!=X48|r2_relset_1(X45,X46,X47,X48)|(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 7.72/7.91  cnf(c_0_134, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_122, c_0_123])).
% 7.72/7.91  cnf(c_0_135, negated_conjecture, (k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126])])).
% 7.72/7.91  cnf(c_0_136, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))))), inference(rw,[status(thm)],[c_0_37, c_0_118])).
% 7.72/7.91  fof(c_0_137, plain, ![X50, X51, X52, X53, X54, X55]:((v1_funct_1(k1_partfun1(X50,X51,X52,X53,X54,X55))|(~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|~v1_funct_1(X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&(m1_subset_1(k1_partfun1(X50,X51,X52,X53,X54,X55),k1_zfmisc_1(k2_zfmisc_1(X50,X53)))|(~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|~v1_funct_1(X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 7.72/7.91  cnf(c_0_138, plain, (k5_relat_1(X1,k4_relat_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_127, c_0_68])).
% 7.72/7.91  cnf(c_0_139, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_84]), c_0_80]), c_0_48])])).
% 7.72/7.91  cnf(c_0_140, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k6_relat_1(X1))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_82]), c_0_79]), c_0_80]), c_0_48])])).
% 7.72/7.91  cnf(c_0_141, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_131])).
% 7.72/7.91  cnf(c_0_142, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_132])).
% 7.72/7.91  cnf(c_0_143, plain, (k4_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_60]), c_0_64])).
% 7.72/7.91  cnf(c_0_144, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_133])).
% 7.72/7.91  cnf(c_0_145, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_118]), c_0_118])).
% 7.72/7.91  cnf(c_0_146, negated_conjecture, (k1_partfun1(esk1_0,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_80])])).
% 7.72/7.91  cnf(c_0_147, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_137])).
% 7.72/7.91  cnf(c_0_148, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_117])).
% 7.72/7.91  cnf(c_0_149, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_117]), c_0_38])])).
% 7.72/7.91  cnf(c_0_150, negated_conjecture, (k5_relat_1(esk3_0,k4_relat_1(esk3_0))=k6_relat_1(k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_48]), c_0_79]), c_0_80])])).
% 7.72/7.91  cnf(c_0_151, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_72]), c_0_80]), c_0_48])])).
% 7.72/7.91  cnf(c_0_152, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_72]), c_0_80]), c_0_48])])).
% 7.72/7.91  cnf(c_0_153, negated_conjecture, (k5_relat_1(esk3_0,k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_48]), c_0_82])).
% 7.72/7.91  cnf(c_0_154, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_60]), c_0_142])).
% 7.72/7.91  cnf(c_0_155, negated_conjecture, (k4_relat_1(k5_relat_1(esk3_0,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X1),k4_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_143, c_0_48])).
% 7.72/7.91  cnf(c_0_156, plain, (k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1))))=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_141, c_0_72])).
% 7.72/7.91  cnf(c_0_157, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_144, c_0_46])).
% 7.72/7.91  cnf(c_0_158, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_145, c_0_146])).
% 7.72/7.91  cnf(c_0_159, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k9_relat_1(esk3_0,k1_relat_1(esk3_0)),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_125]), c_0_126])])).
% 7.72/7.91  cnf(c_0_160, plain, (k5_relat_1(k4_relat_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_130, c_0_68])).
% 7.72/7.91  cnf(c_0_161, negated_conjecture, (k7_relat_1(esk4_0,esk2_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_148]), c_0_149])])).
% 7.72/7.91  cnf(c_0_162, negated_conjecture, (k7_relat_1(esk4_0,X1)=k5_relat_1(k6_relat_1(X1),esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_149])).
% 7.72/7.91  cnf(c_0_163, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),k4_relat_1(esk3_0))=k5_relat_1(X1,k6_relat_1(k1_relat_1(esk3_0)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_94]), c_0_150])).
% 7.72/7.91  cnf(c_0_164, negated_conjecture, (v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_151]), c_0_38])])).
% 7.72/7.91  cnf(c_0_165, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),esk3_0)=k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154])).
% 7.72/7.91  cnf(c_0_166, negated_conjecture, (k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k4_relat_1(esk3_0))=k4_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_155, c_0_153])).
% 7.72/7.91  cnf(c_0_167, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_120]), c_0_80]), c_0_48])])).
% 7.72/7.91  cnf(c_0_168, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_157, c_0_158])).
% 7.72/7.91  cnf(c_0_169, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_136]), c_0_146]), c_0_80])])).
% 7.72/7.91  cnf(c_0_170, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0)=k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_121, c_0_149])).
% 7.72/7.91  cnf(c_0_171, negated_conjecture, (k5_relat_1(k4_relat_1(esk3_0),esk3_0)=k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_48]), c_0_82]), c_0_79]), c_0_80])])).
% 7.72/7.91  cnf(c_0_172, negated_conjecture, (k5_relat_1(k6_relat_1(k9_relat_1(esk3_0,k1_relat_1(esk3_0))),esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_161, c_0_118]), c_0_162])).
% 7.72/7.91  cnf(c_0_173, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.72/7.91  cnf(c_0_174, negated_conjecture, (k2_funct_1(esk3_0)=k4_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_165]), c_0_166]), c_0_167])).
% 7.72/7.91  cnf(c_0_175, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_168, c_0_169])])).
% 7.72/7.91  cnf(c_0_176, negated_conjecture, (k5_relat_1(k4_relat_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_171]), c_0_172]), c_0_94])])).
% 7.72/7.91  cnf(c_0_177, negated_conjecture, (esk4_0!=k4_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_173, c_0_174])).
% 7.72/7.91  cnf(c_0_178, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_175]), c_0_176]), c_0_177]), ['proof']).
% 7.72/7.91  # SZS output end CNFRefutation
% 7.72/7.91  # Proof object total steps             : 179
% 7.72/7.91  # Proof object clause steps            : 120
% 7.72/7.91  # Proof object formula steps           : 59
% 7.72/7.91  # Proof object conjectures             : 71
% 7.72/7.91  # Proof object clause conjectures      : 68
% 7.72/7.91  # Proof object formula conjectures     : 3
% 7.72/7.91  # Proof object initial clauses used    : 39
% 7.72/7.91  # Proof object initial formulas used   : 29
% 7.72/7.91  # Proof object generating inferences   : 70
% 7.72/7.91  # Proof object simplifying inferences  : 120
% 7.72/7.91  # Training examples: 0 positive, 0 negative
% 7.72/7.91  # Parsed axioms                        : 29
% 7.72/7.91  # Removed by relevancy pruning/SinE    : 0
% 7.72/7.91  # Initial clauses                      : 51
% 7.72/7.91  # Removed in clause preprocessing      : 2
% 7.72/7.91  # Initial clauses in saturation        : 49
% 7.72/7.91  # Processed clauses                    : 17396
% 7.72/7.91  # ...of these trivial                  : 1390
% 7.72/7.91  # ...subsumed                          : 8186
% 7.72/7.91  # ...remaining for further processing  : 7820
% 7.72/7.91  # Other redundant clauses eliminated   : 3
% 7.72/7.91  # Clauses deleted for lack of memory   : 0
% 7.72/7.91  # Backward-subsumed                    : 148
% 7.72/7.91  # Backward-rewritten                   : 725
% 7.72/7.91  # Generated clauses                    : 575451
% 7.72/7.91  # ...of the previous two non-trivial   : 563493
% 7.72/7.91  # Contextual simplify-reflections      : 0
% 7.72/7.91  # Paramodulations                      : 575448
% 7.72/7.91  # Factorizations                       : 0
% 7.72/7.91  # Equation resolutions                 : 3
% 7.72/7.91  # Propositional unsat checks           : 0
% 7.72/7.91  #    Propositional check models        : 0
% 7.72/7.91  #    Propositional check unsatisfiable : 0
% 7.72/7.91  #    Propositional clauses             : 0
% 7.72/7.91  #    Propositional clauses after purity: 0
% 7.72/7.91  #    Propositional unsat core size     : 0
% 7.72/7.91  #    Propositional preprocessing time  : 0.000
% 7.72/7.91  #    Propositional encoding time       : 0.000
% 7.72/7.91  #    Propositional solver time         : 0.000
% 7.72/7.91  #    Success case prop preproc time    : 0.000
% 7.72/7.91  #    Success case prop encoding time   : 0.000
% 7.72/7.91  #    Success case prop solver time     : 0.000
% 7.72/7.91  # Current number of processed clauses  : 6944
% 7.72/7.91  #    Positive orientable unit clauses  : 1585
% 7.72/7.91  #    Positive unorientable unit clauses: 29
% 7.72/7.91  #    Negative unit clauses             : 3
% 7.72/7.91  #    Non-unit-clauses                  : 5327
% 7.72/7.91  # Current number of unprocessed clauses: 543741
% 7.72/7.91  # ...number of literals in the above   : 2124072
% 7.72/7.91  # Current number of archived formulas  : 0
% 7.72/7.91  # Current number of archived clauses   : 874
% 7.72/7.91  # Clause-clause subsumption calls (NU) : 954486
% 7.72/7.91  # Rec. Clause-clause subsumption calls : 780682
% 7.72/7.91  # Non-unit clause-clause subsumptions  : 8043
% 7.72/7.91  # Unit Clause-clause subsumption calls : 9182
% 7.72/7.91  # Rewrite failures with RHS unbound    : 0
% 7.72/7.91  # BW rewrite match attempts            : 21116
% 7.72/7.91  # BW rewrite match successes           : 399
% 7.72/7.91  # Condensation attempts                : 0
% 7.72/7.91  # Condensation successes               : 0
% 7.72/7.91  # Termbank termtop insertions          : 20318617
% 7.76/7.93  
% 7.76/7.93  # -------------------------------------------------
% 7.76/7.93  # User time                : 7.281 s
% 7.76/7.93  # System time              : 0.318 s
% 7.76/7.93  # Total time               : 7.599 s
% 7.76/7.93  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
