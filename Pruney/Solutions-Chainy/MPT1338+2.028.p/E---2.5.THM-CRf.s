%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:34 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  136 (1660 expanded)
%              Number of clauses        :   96 ( 657 expanded)
%              Number of leaves         :   20 ( 409 expanded)
%              Depth                    :   24
%              Number of atoms          :  465 (8579 expanded)
%              Number of equality atoms :  156 (2244 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t62_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

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

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,plain,(
    ! [X27,X28] :
      ( ( ~ v1_partfun1(X28,X27)
        | k1_relat_1(X28) = X27
        | ~ v1_relat_1(X28)
        | ~ v4_relat_1(X28,X27) )
      & ( k1_relat_1(X28) != X27
        | v1_partfun1(X28,X27)
        | ~ v1_relat_1(X28)
        | ~ v4_relat_1(X28,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_21,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_22,plain,(
    ! [X7] :
      ( ( k2_relat_1(X7) = k1_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) )
      & ( k1_relat_1(X7) = k2_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] :
      ( ( v4_relat_1(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v5_relat_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_24,plain,(
    ! [X36] :
      ( ( v1_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( v1_funct_2(X36,k1_relat_1(X36),k2_relat_1(X36))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X36),k2_relat_1(X36))))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3) )
                 => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_tops_2])).

cnf(c_0_26,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k2_relset_1(X17,X18,X19) = k2_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_31,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk2_0)
      | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

fof(c_0_32,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_33,plain,
    ( v1_partfun1(k4_relat_1(X1),k2_relat_1(X1))
    | ~ v4_relat_1(k4_relat_1(X1),k1_relat_1(k4_relat_1(X1)))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( v1_partfun1(k4_relat_1(X1),k2_relat_1(X1))
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk3_0) = k2_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(pm,[status(thm)],[c_0_38,c_0_36])).

fof(c_0_42,plain,(
    ! [X37] :
      ( ~ l1_struct_0(X37)
      | k2_struct_0(X37) = u1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_43,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,X39,X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_relset_1(X39,X40,X41) != X40
      | ~ v2_funct_1(X41)
      | k2_tops_2(X39,X40,X41) = k2_funct_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_44,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( v1_partfun1(k4_relat_1(esk3_0),k2_struct_0(esk2_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_46,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( v4_relat_1(k4_relat_1(X1),k2_relat_1(X1))
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_49,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,plain,
    ( X1 = k2_relat_1(X2)
    | ~ v1_partfun1(k4_relat_1(X2),X1)
    | ~ v4_relat_1(k4_relat_1(X2),X1)
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(pm,[status(thm)],[c_0_27,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v1_partfun1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_55,negated_conjecture,
    ( v4_relat_1(k4_relat_1(esk3_0),k2_struct_0(esk2_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_40]),c_0_41])])).

fof(c_0_56,plain,(
    ! [X10] :
      ( ( v1_relat_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_57,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9)
      | k2_funct_1(X9) = k4_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_funct_1(esk3_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_49,c_0_36]),c_0_37]),c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0)
    | ~ v4_relat_1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_54]),c_0_40]),c_0_41])])).

cnf(c_0_61,negated_conjecture,
    ( v4_relat_1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_46]),c_0_47])])).

cnf(c_0_62,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = u1_struct_0(esk2_0)
    | ~ v4_relat_1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_44,c_0_54])).

fof(c_0_65,plain,(
    ! [X33,X34,X35] :
      ( ( k5_relat_1(X35,k2_funct_1(X35)) = k6_partfun1(X33)
        | X34 = k1_xboole_0
        | k2_relset_1(X33,X34,X35) != X34
        | ~ v2_funct_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( k5_relat_1(k2_funct_1(X35),X35) = k6_partfun1(X34)
        | X34 = k1_xboole_0
        | k2_relset_1(X33,X34,X35) != X34
        | ~ v2_funct_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_66,plain,(
    ! [X29] : k6_partfun1(X29) = k6_relat_1(X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_67,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk1_0)
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = u1_struct_0(esk2_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_72,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),k2_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_29,c_0_40]),c_0_52]),c_0_41])])).

cnf(c_0_75,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_76,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_67,c_0_59])).

cnf(c_0_77,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68,c_0_69]),c_0_51]),c_0_52]),c_0_41])])).

cnf(c_0_78,plain,
    ( v1_funct_1(k4_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_70,c_0_63])).

fof(c_0_79,plain,(
    ! [X24,X25,X26] :
      ( ( k7_relset_1(X24,X25,X26,X24) = k2_relset_1(X24,X25,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( k8_relset_1(X24,X25,X26,X25) = k1_relset_1(X24,X25,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_80,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k8_relset_1(X20,X21,X22,X23) = k10_relat_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_81,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = u1_struct_0(esk2_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71,c_0_69]),c_0_51]),c_0_52]),c_0_41])])).

fof(c_0_83,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k1_relat_1(k5_relat_1(X5,X6)) = k10_relat_1(X5,k1_relat_1(X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_84,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( k2_relset_1(k1_relat_1(esk3_0),k2_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35,c_0_74]),c_0_40])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_relat_1(esk3_0),k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_40]),c_0_52]),c_0_41])])).

fof(c_0_87,plain,(
    ! [X8] :
      ( k1_relat_1(k6_relat_1(X8)) = X8
      & k2_relat_1(k6_relat_1(X8)) = X8 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_88,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_relat_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_63]),c_0_51]),c_0_52]),c_0_41])])).

cnf(c_0_89,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_78]),c_0_51]),c_0_52]),c_0_41])])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ v1_partfun1(X3,X2)
    | ~ v1_partfun1(X3,X1)
    | ~ v4_relat_1(X3,X2)
    | ~ v4_relat_1(X3,X1)
    | ~ v1_relat_1(X3) ),
    inference(pm,[status(thm)],[c_0_44,c_0_44])).

cnf(c_0_91,negated_conjecture,
    ( v1_partfun1(esk3_0,X1)
    | k1_relat_1(esk3_0) != X1
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(pm,[status(thm)],[c_0_21,c_0_41])).

cnf(c_0_92,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_93,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_94,plain,
    ( m1_subset_1(k4_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(X1)),k1_relat_1(X1))))
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_29,c_0_81])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_78]),c_0_51]),c_0_52]),c_0_41])])).

cnf(c_0_96,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_97,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(k2_struct_0(esk2_0))
    | k2_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84,c_0_74]),c_0_85]),c_0_86]),c_0_51]),c_0_52])])).

cnf(c_0_98,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_99,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_relat_1(esk3_0)) != u1_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_89])])).

cnf(c_0_100,negated_conjecture,
    ( X1 = X2
    | k1_relat_1(esk3_0) != X1
    | ~ v1_partfun1(esk3_0,X2)
    | ~ v4_relat_1(esk3_0,X2)
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90,c_0_91]),c_0_41])])).

cnf(c_0_101,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(pm,[status(thm)],[c_0_28,c_0_36])).

cnf(c_0_102,plain,
    ( k1_relset_1(X1,X2,X3) = k10_relat_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(pm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k4_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k1_relat_1(esk3_0))))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94,c_0_95]),c_0_41])])).

cnf(c_0_104,negated_conjecture,
    ( v4_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_28,c_0_74])).

cnf(c_0_105,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk3_0),k1_relat_1(esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_41])])).

cnf(c_0_106,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k1_relset_1(u1_struct_0(esk2_0),X1,k4_relat_1(esk3_0)) != u1_struct_0(esk2_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | ~ v1_partfun1(esk3_0,X1)
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99,c_0_100]),c_0_101])])).

cnf(c_0_107,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),k1_relat_1(esk3_0),k4_relat_1(esk3_0)) = k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( v1_partfun1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_91]),c_0_104])])).

cnf(c_0_109,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0)) = k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_105,c_0_63]),c_0_51]),c_0_52]),c_0_41])])).

fof(c_0_110,plain,(
    ! [X30,X31,X32] :
      ( ( X31 = k1_xboole_0
        | v1_partfun1(X32,X30)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_xboole_0
        | v1_partfun1(X32,X30)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

cnf(c_0_111,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0)) != u1_struct_0(esk2_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106,c_0_107]),c_0_108]),c_0_104])])).

cnf(c_0_112,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),k1_relat_1(esk3_0),k4_relat_1(esk3_0)) = k2_relat_1(k4_relat_1(esk3_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_35,c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0)) = u1_struct_0(esk2_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_89]),c_0_89])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_relat_1(esk3_0)) != k2_struct_0(esk1_0)
    | k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0)) != u1_struct_0(esk2_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111,c_0_63]),c_0_51]),c_0_52]),c_0_41])])).

cnf(c_0_116,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),X1,k4_relat_1(esk3_0)) = k2_relat_1(k4_relat_1(esk3_0))
    | ~ v1_partfun1(esk3_0,X1)
    | ~ v4_relat_1(esk3_0,X1)
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112,c_0_44]),c_0_41])])).

cnf(c_0_117,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk3_0),X1) = u1_struct_0(esk2_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_partfun1(esk3_0,X1)
    | ~ v4_relat_1(esk3_0,X1)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_113,c_0_44]),c_0_41])])).

cnf(c_0_118,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0)) != u1_struct_0(esk2_0)
    | k2_relat_1(k4_relat_1(esk3_0)) != k2_struct_0(esk1_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | ~ v1_partfun1(esk3_0,u1_struct_0(esk1_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115,c_0_116]),c_0_101])])).

cnf(c_0_120,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk3_0),X1) = u1_struct_0(esk2_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_partfun1(esk3_0,X1)
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_117,c_0_62]),c_0_52]),c_0_41])])).

cnf(c_0_121,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_partfun1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118,c_0_36]),c_0_50]),c_0_52])])).

cnf(c_0_122,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_relat_1(k4_relat_1(esk3_0)) != k2_struct_0(esk1_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | ~ v1_partfun1(esk3_0,u1_struct_0(esk1_0))
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_119,c_0_120]),c_0_108]),c_0_104])])).

cnf(c_0_123,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_relat_1(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44,c_0_121]),c_0_101]),c_0_41])])).

cnf(c_0_124,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_relat_1(k4_relat_1(esk3_0)) != k2_struct_0(esk1_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0))
    | ~ v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122,c_0_123]),c_0_108])])).

cnf(c_0_125,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_relat_1(k4_relat_1(esk3_0)) != k2_struct_0(esk1_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | ~ v1_funct_1(k4_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_124,c_0_69]),c_0_51]),c_0_52]),c_0_41])])).

cnf(c_0_126,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_relat_1(k4_relat_1(esk3_0)) != k2_struct_0(esk1_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125,c_0_78]),c_0_51]),c_0_52]),c_0_41])])).

cnf(c_0_127,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_126,c_0_81]),c_0_41])])).

cnf(c_0_128,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_129,plain,(
    ! [X38] :
      ( v2_struct_0(X38)
      | ~ l1_struct_0(X38)
      | ~ v1_xboole_0(u1_struct_0(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(esk1_0) != k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_127,c_0_46]),c_0_128])])).

cnf(c_0_131,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_130,c_0_123])).

cnf(c_0_133,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_134,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_131,c_0_132]),c_0_133]),c_0_47])]),c_0_134]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.38/1.61  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 1.38/1.61  # and selection function NoSelection.
% 1.38/1.61  #
% 1.38/1.61  # Preprocessing time       : 0.029 s
% 1.38/1.61  
% 1.38/1.61  # Proof found!
% 1.38/1.61  # SZS status Theorem
% 1.38/1.61  # SZS output start CNFRefutation
% 1.38/1.61  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 1.38/1.61  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 1.38/1.61  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.38/1.61  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 1.38/1.61  fof(t62_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 1.38/1.61  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.38/1.61  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.38/1.61  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 1.38/1.61  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 1.38/1.61  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.38/1.61  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 1.38/1.61  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 1.38/1.61  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.38/1.61  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 1.38/1.61  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.38/1.61  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 1.38/1.61  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.38/1.61  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 1.38/1.61  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.38/1.61  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.38/1.61  fof(c_0_20, plain, ![X27, X28]:((~v1_partfun1(X28,X27)|k1_relat_1(X28)=X27|(~v1_relat_1(X28)|~v4_relat_1(X28,X27)))&(k1_relat_1(X28)!=X27|v1_partfun1(X28,X27)|(~v1_relat_1(X28)|~v4_relat_1(X28,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 1.38/1.61  cnf(c_0_21, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.38/1.61  fof(c_0_22, plain, ![X7]:((k2_relat_1(X7)=k1_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))&(k1_relat_1(X7)=k2_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 1.38/1.61  fof(c_0_23, plain, ![X14, X15, X16]:((v4_relat_1(X16,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))&(v5_relat_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.38/1.61  fof(c_0_24, plain, ![X36]:(((v1_funct_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(v1_funct_2(X36,k1_relat_1(X36),k2_relat_1(X36))|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X36),k2_relat_1(X36))))|(~v1_relat_1(X36)|~v1_funct_1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 1.38/1.61  fof(c_0_25, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t62_tops_2])).
% 1.38/1.61  cnf(c_0_26, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_21])).
% 1.38/1.61  cnf(c_0_27, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.38/1.61  cnf(c_0_28, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.38/1.61  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.38/1.61  fof(c_0_30, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|k2_relset_1(X17,X18,X19)=k2_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.38/1.61  fof(c_0_31, negated_conjecture, (l1_struct_0(esk1_0)&((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)&v2_funct_1(esk3_0))&(k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).
% 1.38/1.61  fof(c_0_32, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.38/1.61  cnf(c_0_33, plain, (v1_partfun1(k4_relat_1(X1),k2_relat_1(X1))|~v4_relat_1(k4_relat_1(X1),k1_relat_1(k4_relat_1(X1)))|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_26, c_0_27])).
% 1.38/1.61  cnf(c_0_34, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_28, c_0_29])).
% 1.38/1.61  cnf(c_0_35, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.38/1.61  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_37, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.38/1.61  cnf(c_0_39, plain, (v1_partfun1(k4_relat_1(X1),k2_relat_1(X1))|~v1_funct_1(k4_relat_1(X1))|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_33, c_0_34])).
% 1.38/1.61  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk3_0)=k2_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 1.38/1.61  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk3_0)), inference(pm,[status(thm)],[c_0_38, c_0_36])).
% 1.38/1.61  fof(c_0_42, plain, ![X37]:(~l1_struct_0(X37)|k2_struct_0(X37)=u1_struct_0(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 1.38/1.61  fof(c_0_43, plain, ![X39, X40, X41]:(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|(k2_relset_1(X39,X40,X41)!=X40|~v2_funct_1(X41)|k2_tops_2(X39,X40,X41)=k2_funct_1(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 1.38/1.61  cnf(c_0_44, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.38/1.61  cnf(c_0_45, negated_conjecture, (v1_partfun1(k4_relat_1(esk3_0),k2_struct_0(esk2_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 1.38/1.61  cnf(c_0_46, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.38/1.61  cnf(c_0_47, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_48, plain, (v4_relat_1(k4_relat_1(X1),k2_relat_1(X1))|~v1_funct_1(k4_relat_1(X1))|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_34, c_0_27])).
% 1.38/1.61  cnf(c_0_49, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.38/1.61  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_51, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_53, plain, (X1=k2_relat_1(X2)|~v1_partfun1(k4_relat_1(X2),X1)|~v4_relat_1(k4_relat_1(X2),X1)|~v1_relat_1(k4_relat_1(X2))|~v1_relat_1(X2)), inference(pm,[status(thm)],[c_0_27, c_0_44])).
% 1.38/1.61  cnf(c_0_54, negated_conjecture, (v1_partfun1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 1.38/1.61  cnf(c_0_55, negated_conjecture, (v4_relat_1(k4_relat_1(esk3_0),k2_struct_0(esk2_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_40]), c_0_41])])).
% 1.38/1.61  fof(c_0_56, plain, ![X10]:((v1_relat_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.38/1.61  fof(c_0_57, plain, ![X9]:(~v1_relat_1(X9)|~v1_funct_1(X9)|(~v2_funct_1(X9)|k2_funct_1(X9)=k4_relat_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 1.38/1.61  cnf(c_0_58, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_59, negated_conjecture, (k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_funct_1(esk3_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_49, c_0_36]), c_0_37]), c_0_50]), c_0_51]), c_0_52])])).
% 1.38/1.61  cnf(c_0_60, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)|~v4_relat_1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_54]), c_0_40]), c_0_41])])).
% 1.38/1.61  cnf(c_0_61, negated_conjecture, (v4_relat_1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_46]), c_0_47])])).
% 1.38/1.61  cnf(c_0_62, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.38/1.61  cnf(c_0_63, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.38/1.61  cnf(c_0_64, negated_conjecture, (k1_relat_1(k4_relat_1(esk3_0))=u1_struct_0(esk2_0)|~v4_relat_1(k4_relat_1(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(pm,[status(thm)],[c_0_44, c_0_54])).
% 1.38/1.61  fof(c_0_65, plain, ![X33, X34, X35]:((k5_relat_1(X35,k2_funct_1(X35))=k6_partfun1(X33)|X34=k1_xboole_0|(k2_relset_1(X33,X34,X35)!=X34|~v2_funct_1(X35))|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&(k5_relat_1(k2_funct_1(X35),X35)=k6_partfun1(X34)|X34=k1_xboole_0|(k2_relset_1(X33,X34,X35)!=X34|~v2_funct_1(X35))|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 1.38/1.61  fof(c_0_66, plain, ![X29]:k6_partfun1(X29)=k6_relat_1(X29), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 1.38/1.61  cnf(c_0_67, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk1_0)|k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_58, c_0_59])).
% 1.38/1.61  cnf(c_0_68, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 1.38/1.61  cnf(c_0_69, plain, (v1_relat_1(k4_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_62, c_0_63])).
% 1.38/1.61  cnf(c_0_70, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.38/1.61  cnf(c_0_71, negated_conjecture, (k1_relat_1(k4_relat_1(esk3_0))=u1_struct_0(esk2_0)|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(pm,[status(thm)],[c_0_64, c_0_61])).
% 1.38/1.61  cnf(c_0_72, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.38/1.61  cnf(c_0_73, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.38/1.61  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),k2_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_29, c_0_40]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_75, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.38/1.61  cnf(c_0_76, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_67, c_0_59])).
% 1.38/1.61  cnf(c_0_77, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)|~v1_funct_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68, c_0_69]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_78, plain, (v1_funct_1(k4_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_70, c_0_63])).
% 1.38/1.61  fof(c_0_79, plain, ![X24, X25, X26]:((k7_relset_1(X24,X25,X26,X24)=k2_relset_1(X24,X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(k8_relset_1(X24,X25,X26,X25)=k1_relset_1(X24,X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 1.38/1.61  fof(c_0_80, plain, ![X20, X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k8_relset_1(X20,X21,X22,X23)=k10_relat_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 1.38/1.61  cnf(c_0_81, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.38/1.61  cnf(c_0_82, negated_conjecture, (k1_relat_1(k4_relat_1(esk3_0))=u1_struct_0(esk2_0)|~v1_funct_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71, c_0_69]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  fof(c_0_83, plain, ![X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|k1_relat_1(k5_relat_1(X5,X6))=k10_relat_1(X5,k1_relat_1(X6)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 1.38/1.61  cnf(c_0_84, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 1.38/1.61  cnf(c_0_85, negated_conjecture, (k2_relset_1(k1_relat_1(esk3_0),k2_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35, c_0_74]), c_0_40])).
% 1.38/1.61  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk3_0,k1_relat_1(esk3_0),k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_40]), c_0_52]), c_0_41])])).
% 1.38/1.61  fof(c_0_87, plain, ![X8]:(k1_relat_1(k6_relat_1(X8))=X8&k2_relat_1(k6_relat_1(X8))=X8), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.38/1.61  cnf(c_0_88, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_relat_1(esk3_0))!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_63]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_89, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_78]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_90, plain, (X1=X2|~v1_partfun1(X3,X2)|~v1_partfun1(X3,X1)|~v4_relat_1(X3,X2)|~v4_relat_1(X3,X1)|~v1_relat_1(X3)), inference(pm,[status(thm)],[c_0_44, c_0_44])).
% 1.38/1.61  cnf(c_0_91, negated_conjecture, (v1_partfun1(esk3_0,X1)|k1_relat_1(esk3_0)!=X1|~v4_relat_1(esk3_0,X1)), inference(pm,[status(thm)],[c_0_21, c_0_41])).
% 1.38/1.61  cnf(c_0_92, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 1.38/1.61  cnf(c_0_93, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.38/1.61  cnf(c_0_94, plain, (m1_subset_1(k4_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(X1)),k1_relat_1(X1))))|~v1_funct_1(k4_relat_1(X1))|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_29, c_0_81])).
% 1.38/1.61  cnf(c_0_95, negated_conjecture, (k1_relat_1(k4_relat_1(esk3_0))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_78]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_96, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.38/1.61  cnf(c_0_97, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),esk3_0)=k6_relat_1(k2_struct_0(esk2_0))|k2_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84, c_0_74]), c_0_85]), c_0_86]), c_0_51]), c_0_52])])).
% 1.38/1.61  cnf(c_0_98, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 1.38/1.61  cnf(c_0_99, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_relat_1(esk3_0))!=u1_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_89])])).
% 1.38/1.61  cnf(c_0_100, negated_conjecture, (X1=X2|k1_relat_1(esk3_0)!=X1|~v1_partfun1(esk3_0,X2)|~v4_relat_1(esk3_0,X2)|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90, c_0_91]), c_0_41])])).
% 1.38/1.61  cnf(c_0_101, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(pm,[status(thm)],[c_0_28, c_0_36])).
% 1.38/1.61  cnf(c_0_102, plain, (k1_relset_1(X1,X2,X3)=k10_relat_1(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(pm,[status(thm)],[c_0_92, c_0_93])).
% 1.38/1.61  cnf(c_0_103, negated_conjecture, (m1_subset_1(k4_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k1_relat_1(esk3_0))))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94, c_0_95]), c_0_41])])).
% 1.38/1.61  cnf(c_0_104, negated_conjecture, (v4_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(pm,[status(thm)],[c_0_28, c_0_74])).
% 1.38/1.61  cnf(c_0_105, negated_conjecture, (k10_relat_1(k2_funct_1(esk3_0),k1_relat_1(esk3_0))=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)=k1_xboole_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_41])])).
% 1.38/1.61  cnf(c_0_106, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k1_relset_1(u1_struct_0(esk2_0),X1,k4_relat_1(esk3_0))!=u1_struct_0(esk2_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|~v1_partfun1(esk3_0,X1)|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99, c_0_100]), c_0_101])])).
% 1.38/1.61  cnf(c_0_107, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),k1_relat_1(esk3_0),k4_relat_1(esk3_0))=k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(pm,[status(thm)],[c_0_102, c_0_103])).
% 1.38/1.61  cnf(c_0_108, negated_conjecture, (v1_partfun1(esk3_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_91]), c_0_104])])).
% 1.38/1.61  cnf(c_0_109, negated_conjecture, (k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0))=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)=k1_xboole_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_105, c_0_63]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  fof(c_0_110, plain, ![X30, X31, X32]:((X31=k1_xboole_0|v1_partfun1(X32,X30)|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X30!=k1_xboole_0|v1_partfun1(X32,X30)|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 1.38/1.61  cnf(c_0_111, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0))!=u1_struct_0(esk2_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106, c_0_107]), c_0_108]), c_0_104])])).
% 1.38/1.61  cnf(c_0_112, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),k1_relat_1(esk3_0),k4_relat_1(esk3_0))=k2_relat_1(k4_relat_1(esk3_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(pm,[status(thm)],[c_0_35, c_0_103])).
% 1.38/1.61  cnf(c_0_113, negated_conjecture, (k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0))=u1_struct_0(esk2_0)|u1_struct_0(esk2_0)=k1_xboole_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_89]), c_0_89])).
% 1.38/1.61  cnf(c_0_114, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 1.38/1.61  cnf(c_0_115, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_relat_1(esk3_0))!=k2_struct_0(esk1_0)|k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0))!=u1_struct_0(esk2_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111, c_0_63]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_116, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),X1,k4_relat_1(esk3_0))=k2_relat_1(k4_relat_1(esk3_0))|~v1_partfun1(esk3_0,X1)|~v4_relat_1(esk3_0,X1)|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112, c_0_44]), c_0_41])])).
% 1.38/1.61  cnf(c_0_117, negated_conjecture, (k10_relat_1(k4_relat_1(esk3_0),X1)=u1_struct_0(esk2_0)|u1_struct_0(esk2_0)=k1_xboole_0|~v1_partfun1(esk3_0,X1)|~v4_relat_1(esk3_0,X1)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_113, c_0_44]), c_0_41])])).
% 1.38/1.61  cnf(c_0_118, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_114])).
% 1.38/1.61  cnf(c_0_119, negated_conjecture, (k10_relat_1(k4_relat_1(esk3_0),k1_relat_1(esk3_0))!=u1_struct_0(esk2_0)|k2_relat_1(k4_relat_1(esk3_0))!=k2_struct_0(esk1_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|~v1_partfun1(esk3_0,u1_struct_0(esk1_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115, c_0_116]), c_0_101])])).
% 1.38/1.61  cnf(c_0_120, negated_conjecture, (k10_relat_1(k4_relat_1(esk3_0),X1)=u1_struct_0(esk2_0)|u1_struct_0(esk2_0)=k1_xboole_0|~v1_partfun1(esk3_0,X1)|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_117, c_0_62]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_121, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_partfun1(esk3_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118, c_0_36]), c_0_50]), c_0_52])])).
% 1.38/1.61  cnf(c_0_122, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|k2_relat_1(k4_relat_1(esk3_0))!=k2_struct_0(esk1_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|~v1_partfun1(esk3_0,u1_struct_0(esk1_0))|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_119, c_0_120]), c_0_108]), c_0_104])])).
% 1.38/1.61  cnf(c_0_123, negated_conjecture, (u1_struct_0(esk1_0)=k1_relat_1(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44, c_0_121]), c_0_101]), c_0_41])])).
% 1.38/1.61  cnf(c_0_124, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|k2_relat_1(k4_relat_1(esk3_0))!=k2_struct_0(esk1_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|~v1_funct_1(k4_relat_1(esk3_0))|~v1_relat_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122, c_0_123]), c_0_108])])).
% 1.38/1.61  cnf(c_0_125, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|k2_relat_1(k4_relat_1(esk3_0))!=k2_struct_0(esk1_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|~v1_funct_1(k4_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_124, c_0_69]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_126, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|k2_relat_1(k4_relat_1(esk3_0))!=k2_struct_0(esk1_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125, c_0_78]), c_0_51]), c_0_52]), c_0_41])])).
% 1.38/1.61  cnf(c_0_127, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|k2_struct_0(esk1_0)!=k1_relat_1(esk3_0)|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_126, c_0_81]), c_0_41])])).
% 1.38/1.61  cnf(c_0_128, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  fof(c_0_129, plain, ![X38]:(v2_struct_0(X38)|~l1_struct_0(X38)|~v1_xboole_0(u1_struct_0(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 1.38/1.61  cnf(c_0_130, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_127, c_0_46]), c_0_128])])).
% 1.38/1.61  cnf(c_0_131, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_129])).
% 1.38/1.61  cnf(c_0_132, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(pm,[status(thm)],[c_0_130, c_0_123])).
% 1.38/1.61  cnf(c_0_133, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.38/1.61  cnf(c_0_134, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.61  cnf(c_0_135, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_131, c_0_132]), c_0_133]), c_0_47])]), c_0_134]), ['proof']).
% 1.38/1.61  # SZS output end CNFRefutation
% 1.38/1.61  # Proof object total steps             : 136
% 1.38/1.61  # Proof object clause steps            : 96
% 1.38/1.61  # Proof object formula steps           : 40
% 1.38/1.61  # Proof object conjectures             : 63
% 1.38/1.61  # Proof object clause conjectures      : 60
% 1.38/1.61  # Proof object formula conjectures     : 3
% 1.38/1.61  # Proof object initial clauses used    : 32
% 1.38/1.61  # Proof object initial formulas used   : 20
% 1.38/1.61  # Proof object generating inferences   : 60
% 1.38/1.61  # Proof object simplifying inferences  : 114
% 1.38/1.61  # Training examples: 0 positive, 0 negative
% 1.38/1.61  # Parsed axioms                        : 20
% 1.38/1.61  # Removed by relevancy pruning/SinE    : 0
% 1.38/1.61  # Initial clauses                      : 38
% 1.38/1.61  # Removed in clause preprocessing      : 2
% 1.38/1.61  # Initial clauses in saturation        : 36
% 1.38/1.61  # Processed clauses                    : 4116
% 1.38/1.61  # ...of these trivial                  : 33
% 1.38/1.61  # ...subsumed                          : 2662
% 1.38/1.61  # ...remaining for further processing  : 1421
% 1.38/1.61  # Other redundant clauses eliminated   : 0
% 1.38/1.61  # Clauses deleted for lack of memory   : 0
% 1.38/1.61  # Backward-subsumed                    : 92
% 1.38/1.61  # Backward-rewritten                   : 818
% 1.38/1.61  # Generated clauses                    : 77945
% 1.38/1.61  # ...of the previous two non-trivial   : 77311
% 1.38/1.61  # Contextual simplify-reflections      : 0
% 1.38/1.61  # Paramodulations                      : 77879
% 1.38/1.61  # Factorizations                       : 21
% 1.38/1.61  # Equation resolutions                 : 45
% 1.38/1.61  # Propositional unsat checks           : 0
% 1.38/1.61  #    Propositional check models        : 0
% 1.38/1.61  #    Propositional check unsatisfiable : 0
% 1.38/1.61  #    Propositional clauses             : 0
% 1.38/1.61  #    Propositional clauses after purity: 0
% 1.38/1.61  #    Propositional unsat core size     : 0
% 1.38/1.61  #    Propositional preprocessing time  : 0.000
% 1.38/1.61  #    Propositional encoding time       : 0.000
% 1.38/1.61  #    Propositional solver time         : 0.000
% 1.38/1.61  #    Success case prop preproc time    : 0.000
% 1.38/1.61  #    Success case prop encoding time   : 0.000
% 1.38/1.61  #    Success case prop solver time     : 0.000
% 1.38/1.61  # Current number of processed clauses  : 511
% 1.38/1.61  #    Positive orientable unit clauses  : 14
% 1.38/1.61  #    Positive unorientable unit clauses: 0
% 1.38/1.61  #    Negative unit clauses             : 1
% 1.38/1.61  #    Non-unit-clauses                  : 496
% 1.38/1.61  # Current number of unprocessed clauses: 72573
% 1.38/1.61  # ...number of literals in the above   : 752146
% 1.38/1.61  # Current number of archived formulas  : 0
% 1.38/1.61  # Current number of archived clauses   : 911
% 1.38/1.61  # Clause-clause subsumption calls (NU) : 61439
% 1.38/1.61  # Rec. Clause-clause subsumption calls : 15236
% 1.38/1.61  # Non-unit clause-clause subsumptions  : 2750
% 1.38/1.61  # Unit Clause-clause subsumption calls : 54
% 1.38/1.61  # Rewrite failures with RHS unbound    : 0
% 1.38/1.61  # BW rewrite match attempts            : 24
% 1.38/1.61  # BW rewrite match successes           : 17
% 1.38/1.61  # Condensation attempts                : 0
% 1.38/1.61  # Condensation successes               : 0
% 1.38/1.61  # Termbank termtop insertions          : 1308952
% 1.38/1.62  
% 1.38/1.62  # -------------------------------------------------
% 1.38/1.62  # User time                : 1.212 s
% 1.38/1.62  # System time              : 0.057 s
% 1.38/1.62  # Total time               : 1.269 s
% 1.38/1.62  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
