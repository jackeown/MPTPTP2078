%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:20 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 (7165 expanded)
%              Number of clauses        :   72 (2246 expanded)
%              Number of leaves         :   12 (1772 expanded)
%              Depth                    :   15
%              Number of atoms          :  589 (61562 expanded)
%              Number of equality atoms :   63 (1539 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ( v1_funct_1(k7_tmap_1(X1,X2))
              & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
              & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
              & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t55_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => ( v5_pre_topc(X3,X1,X2)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( v3_pre_topc(X4,X2)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(t62_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(t105_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
             => ( X3 = X2
               => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ( v1_funct_1(k7_tmap_1(X1,X2))
                & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
                & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
                & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t113_tmap_1])).

fof(c_0_13,plain,(
    ! [X27,X28] :
      ( ( u1_struct_0(k6_tmap_1(X27,X28)) = u1_struct_0(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( u1_pre_topc(k6_tmap_1(X27,X28)) = k5_tmap_1(X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) )
    & ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))
      | v3_pre_topc(esk3_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ( v1_pre_topc(k6_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( v2_pre_topc(k6_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( l1_pre_topc(k6_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_16,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ v5_pre_topc(X15,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v3_pre_topc(X16,X14)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16),X13)
        | k2_struct_0(X14) = k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | v5_pre_topc(X15,X13,X14)
        | k2_struct_0(X14) = k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( v3_pre_topc(esk1_3(X13,X14,X15),X14)
        | v5_pre_topc(X15,X13,X14)
        | k2_struct_0(X14) = k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,esk1_3(X13,X14,X15)),X13)
        | v5_pre_topc(X15,X13,X14)
        | k2_struct_0(X14) = k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ v5_pre_topc(X15,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v3_pre_topc(X16,X14)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16),X13)
        | k2_struct_0(X13) != k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | v5_pre_topc(X15,X13,X14)
        | k2_struct_0(X13) != k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( v3_pre_topc(esk1_3(X13,X14,X15),X14)
        | v5_pre_topc(X15,X13,X14)
        | k2_struct_0(X13) != k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,esk1_3(X13,X14,X15)),X13)
        | v5_pre_topc(X15,X13,X14)
        | k2_struct_0(X13) != k1_xboole_0
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

cnf(c_0_17,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k8_relset_1(X5,X5,k6_partfun1(X5),X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_24,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_27,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | k7_tmap_1(X18,X19) = k6_partfun1(u1_struct_0(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ( v1_funct_1(k7_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) )
      & ( v1_funct_2(k7_tmap_1(X22,X23),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) )
      & ( m1_subset_1(k7_tmap_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_31,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_33,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v5_pre_topc(X11,X9,X10)
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)),X10)
        | X11 != X12
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10))))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)),X10)
        | v5_pre_topc(X11,X9,X10)
        | X11 != X12
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10))))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_26])])).

cnf(c_0_42,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_26])])).

cnf(c_0_43,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | k2_struct_0(X3) = k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_44,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X29,X30))))
      | X31 != X30
      | v3_pre_topc(X31,k6_tmap_1(X29,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

cnf(c_0_45,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_47,plain,(
    ! [X32,X33] :
      ( ( ~ v3_pre_topc(X33,X32)
        | g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)) = k6_tmap_1(X32,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)) != k6_tmap_1(X32,X33)
        | v3_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_26])])).

cnf(c_0_50,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)
    | ~ v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_19]),c_0_20]),c_0_18])]),c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_26])]),c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_26])])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_61,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_25]),c_0_26])])).

cnf(c_0_63,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_25]),c_0_26])])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_51]),c_0_53]),c_0_26]),c_0_51]),c_0_51])]),c_0_54])])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_52]),c_0_53])])).

fof(c_0_66,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | k2_struct_0(X7) = u1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_67,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | l1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_68,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_28]),c_0_51]),c_0_51]),c_0_52]),c_0_51]),c_0_53]),c_0_20]),c_0_51]),c_0_54])])).

cnf(c_0_69,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_53])])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_25]),c_0_60]),c_0_26])])).

cnf(c_0_73,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_74,negated_conjecture,
    ( v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_25]),c_0_26])]),c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_76,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_77,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0)
    | v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_25]),c_0_19]),c_0_20]),c_0_18])]),c_0_21])).

cnf(c_0_81,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_25]),c_0_25]),c_0_52])])).

cnf(c_0_82,negated_conjecture,
    ( v5_pre_topc(X1,esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_25]),c_0_19]),c_0_20]),c_0_25])])).

cnf(c_0_83,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_54]),c_0_52]),c_0_53])]),c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_25]),c_0_26])])).

cnf(c_0_85,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_18])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_54])])).

cnf(c_0_88,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_52]),c_0_53]),c_0_54])]),c_0_69])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_28]),c_0_51]),c_0_51]),c_0_52]),c_0_51]),c_0_53]),c_0_20]),c_0_51]),c_0_54])])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_25]),c_0_26])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_85]),c_0_20])])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_88])]),c_0_93]),c_0_93])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_80]),c_0_95])]),c_0_91]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:44:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.54  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.038 s
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t113_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.20/0.54  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.20/0.54  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.20/0.54  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 0.20/0.54  fof(t171_funct_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 0.20/0.54  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.20/0.54  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.20/0.54  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.20/0.54  fof(t105_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))=>(X3=X2=>v3_pre_topc(X3,k6_tmap_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tmap_1)).
% 0.20/0.54  fof(t106_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.20/0.54  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.54  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.54  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t113_tmap_1])).
% 0.20/0.54  fof(c_0_13, plain, ![X27, X28]:((u1_struct_0(k6_tmap_1(X27,X28))=u1_struct_0(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(u1_pre_topc(k6_tmap_1(X27,X28))=k5_tmap_1(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.20/0.54  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|(~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))))&((((v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0))&(v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|v3_pre_topc(esk3_0,esk2_0)))&(v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)))&(m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))|v3_pre_topc(esk3_0,esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 0.20/0.54  fof(c_0_15, plain, ![X20, X21]:(((v1_pre_topc(k6_tmap_1(X20,X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))&(v2_pre_topc(k6_tmap_1(X20,X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))))))&(l1_pre_topc(k6_tmap_1(X20,X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.20/0.54  fof(c_0_16, plain, ![X13, X14, X15, X16]:(((~v5_pre_topc(X15,X13,X14)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~v3_pre_topc(X16,X14)|v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16),X13)))|k2_struct_0(X14)=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|v5_pre_topc(X15,X13,X14)|k2_struct_0(X14)=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((v3_pre_topc(esk1_3(X13,X14,X15),X14)|v5_pre_topc(X15,X13,X14)|k2_struct_0(X14)=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,esk1_3(X13,X14,X15)),X13)|v5_pre_topc(X15,X13,X14)|k2_struct_0(X14)=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13)))))&((~v5_pre_topc(X15,X13,X14)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~v3_pre_topc(X16,X14)|v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16),X13)))|k2_struct_0(X13)!=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|v5_pre_topc(X15,X13,X14)|k2_struct_0(X13)!=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((v3_pre_topc(esk1_3(X13,X14,X15),X14)|v5_pre_topc(X15,X13,X14)|k2_struct_0(X13)!=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,esk1_3(X13,X14,X15)),X13)|v5_pre_topc(X15,X13,X14)|k2_struct_0(X13)!=k1_xboole_0|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.20/0.54  cnf(c_0_17, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.54  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  cnf(c_0_22, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.54  fof(c_0_23, plain, ![X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|k8_relset_1(X5,X5,k6_partfun1(X5),X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).
% 0.20/0.54  cnf(c_0_24, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_25, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.54  cnf(c_0_26, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.54  cnf(c_0_27, plain, (v5_pre_topc(X3,X1,X2)|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_28, plain, (k8_relset_1(X2,X2,k6_partfun1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  fof(c_0_29, plain, ![X18, X19]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|k7_tmap_1(X18,X19)=k6_partfun1(u1_struct_0(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.20/0.54  fof(c_0_30, plain, ![X22, X23]:(((v1_funct_1(k7_tmap_1(X22,X23))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))&(v1_funct_2(k7_tmap_1(X22,X23),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))))))&(m1_subset_1(k7_tmap_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.20/0.54  cnf(c_0_31, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_32, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.54  fof(c_0_33, plain, ![X9, X10, X11, X12]:((~v5_pre_topc(X11,X9,X10)|v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)),X10)|X11!=X12|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10)))))|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|(~v2_pre_topc(X10)|~l1_pre_topc(X10))|(~v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)),X10)|v5_pre_topc(X11,X9,X10)|X11!=X12|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))),u1_struct_0(X10)))))|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))))|(~v2_pre_topc(X10)|~l1_pre_topc(X10))|(~v2_pre_topc(X9)|~l1_pre_topc(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.20/0.54  cnf(c_0_34, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_35, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_36, plain, (v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)|k2_struct_0(X1)!=k1_xboole_0|~v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)|~v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))|~v1_funct_1(k6_partfun1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.54  cnf(c_0_37, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.54  cnf(c_0_38, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.54  cnf(c_0_39, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.54  cnf(c_0_40, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.54  cnf(c_0_41, negated_conjecture, (v3_pre_topc(esk1_3(X1,k6_tmap_1(esk2_0,esk3_0),X2),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_42, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_43, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|k2_struct_0(X3)=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  fof(c_0_44, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X29,X30))))|(X31!=X30|v3_pre_topc(X31,k6_tmap_1(X29,X30)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).
% 0.20/0.54  cnf(c_0_45, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.54  cnf(c_0_46, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.54  fof(c_0_47, plain, ![X32, X33]:((~v3_pre_topc(X33,X32)|g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))=k6_tmap_1(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))!=k6_tmap_1(X32,X33)|v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).
% 0.20/0.54  cnf(c_0_48, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_49, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_50, plain, (v5_pre_topc(k6_partfun1(u1_struct_0(X1)),X1,X1)|~v3_pre_topc(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),X1)|~v1_funct_2(k6_partfun1(u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(X1))|~v1_funct_1(k6_partfun1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(k6_partfun1(u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~m1_subset_1(esk1_3(X1,X1,k6_partfun1(u1_struct_0(X1))),k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_28]), c_0_36])).
% 0.20/0.54  cnf(c_0_51, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.54  cnf(c_0_52, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_25]), c_0_19]), c_0_20]), c_0_18])]), c_0_21])).
% 0.20/0.54  cnf(c_0_53, negated_conjecture, (v1_funct_1(k7_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.54  cnf(c_0_54, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_25])).
% 0.20/0.54  cnf(c_0_55, negated_conjecture, (v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_25]), c_0_26])]), c_0_42])).
% 0.20/0.54  cnf(c_0_56, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_57, plain, (v2_struct_0(X1)|v3_pre_topc(X3,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|X3!=X2), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.54  cnf(c_0_58, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  cnf(c_0_59, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.54  cnf(c_0_60, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.54  cnf(c_0_61, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=k6_tmap_1(X2,X1)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.54  cnf(c_0_62, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_63, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_64, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_25]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_51]), c_0_53]), c_0_26]), c_0_51]), c_0_51])]), c_0_54])])).
% 0.20/0.54  cnf(c_0_65, negated_conjecture, (v3_pre_topc(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_54]), c_0_52]), c_0_53])])).
% 0.20/0.54  fof(c_0_66, plain, ![X7]:(~l1_struct_0(X7)|k2_struct_0(X7)=u1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.54  fof(c_0_67, plain, ![X8]:(~l1_pre_topc(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.54  cnf(c_0_68, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_28]), c_0_51]), c_0_51]), c_0_52]), c_0_51]), c_0_53]), c_0_20]), c_0_51]), c_0_54])])).
% 0.20/0.54  cnf(c_0_69, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  cnf(c_0_70, plain, (v2_struct_0(X1)|v3_pre_topc(X2,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.54  cnf(c_0_71, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_53])])).
% 0.20/0.54  cnf(c_0_72, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(esk2_0))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_25]), c_0_60]), c_0_26])])).
% 0.20/0.54  cnf(c_0_73, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.54  cnf(c_0_74, negated_conjecture, (v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_25]), c_0_26])]), c_0_63])).
% 0.20/0.54  cnf(c_0_75, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_3(k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.54  cnf(c_0_76, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_77, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.54  cnf(c_0_78, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.54  cnf(c_0_79, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)|v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.54  cnf(c_0_80, negated_conjecture, (v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_25]), c_0_19]), c_0_20]), c_0_18])]), c_0_21])).
% 0.20/0.54  cnf(c_0_81, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_25]), c_0_25]), c_0_52])])).
% 0.20/0.54  cnf(c_0_82, negated_conjecture, (v5_pre_topc(X1,esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~v5_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_25]), c_0_19]), c_0_20]), c_0_25])])).
% 0.20/0.54  cnf(c_0_83, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_54]), c_0_52]), c_0_53])]), c_0_75])).
% 0.20/0.54  cnf(c_0_84, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|k2_struct_0(X1)!=k1_xboole_0|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_85, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.54  cnf(c_0_86, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_18])])).
% 0.20/0.54  cnf(c_0_87, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_54])])).
% 0.20/0.54  cnf(c_0_88, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_52]), c_0_53]), c_0_54])]), c_0_69])).
% 0.20/0.54  cnf(c_0_89, negated_conjecture, (v3_pre_topc(X1,esk2_0)|k2_struct_0(esk2_0)!=k1_xboole_0|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_28]), c_0_51]), c_0_51]), c_0_52]), c_0_51]), c_0_53]), c_0_20]), c_0_51]), c_0_54])])).
% 0.20/0.54  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_25]), c_0_26])])).
% 0.20/0.54  cnf(c_0_91, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.20/0.54  cnf(c_0_92, negated_conjecture, (v3_pre_topc(X1,esk2_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_85]), c_0_20])])).
% 0.20/0.54  cnf(c_0_93, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.54  cnf(c_0_94, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_88])]), c_0_93]), c_0_93])])).
% 0.20/0.54  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_18, c_0_93])).
% 0.20/0.54  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_80]), c_0_95])]), c_0_91]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 97
% 0.20/0.54  # Proof object clause steps            : 72
% 0.20/0.54  # Proof object formula steps           : 25
% 0.20/0.54  # Proof object conjectures             : 49
% 0.20/0.54  # Proof object clause conjectures      : 46
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 27
% 0.20/0.54  # Proof object initial formulas used   : 12
% 0.20/0.54  # Proof object generating inferences   : 36
% 0.20/0.54  # Proof object simplifying inferences  : 141
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 14
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 40
% 0.20/0.54  # Removed in clause preprocessing      : 0
% 0.20/0.54  # Initial clauses in saturation        : 40
% 0.20/0.54  # Processed clauses                    : 777
% 0.20/0.54  # ...of these trivial                  : 6
% 0.20/0.54  # ...subsumed                          : 356
% 0.20/0.54  # ...remaining for further processing  : 415
% 0.20/0.54  # Other redundant clauses eliminated   : 3
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 29
% 0.20/0.54  # Backward-rewritten                   : 278
% 0.20/0.54  # Generated clauses                    : 2272
% 0.20/0.54  # ...of the previous two non-trivial   : 2352
% 0.20/0.54  # Contextual simplify-reflections      : 200
% 0.20/0.54  # Paramodulations                      : 2267
% 0.20/0.54  # Factorizations                       : 0
% 0.20/0.54  # Equation resolutions                 : 3
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 103
% 0.20/0.54  #    Positive orientable unit clauses  : 17
% 0.20/0.54  #    Positive unorientable unit clauses: 0
% 0.20/0.54  #    Negative unit clauses             : 3
% 0.20/0.54  #    Non-unit-clauses                  : 83
% 0.20/0.54  # Current number of unprocessed clauses: 1488
% 0.20/0.54  # ...number of literals in the above   : 9541
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 309
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 62090
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 6867
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 581
% 0.20/0.54  # Unit Clause-clause subsumption calls : 711
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 14
% 0.20/0.54  # BW rewrite match successes           : 7
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 111526
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.172 s
% 0.20/0.54  # System time              : 0.012 s
% 0.20/0.54  # Total time               : 0.183 s
% 0.20/0.54  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
