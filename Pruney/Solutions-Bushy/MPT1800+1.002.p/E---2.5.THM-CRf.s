%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1800+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:47 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 252 expanded)
%              Number of clauses        :   35 (  96 expanded)
%              Number of leaves         :    6 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  289 (1872 expanded)
%              Number of equality atoms :   43 ( 268 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(d1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tsep_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_tmap_1])).

fof(c_0_7,plain,(
    ! [X16,X17] :
      ( ( ~ v3_pre_topc(X17,X16)
        | g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)) = k6_tmap_1(X16,X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)) != k6_tmap_1(X16,X17)
        | v3_pre_topc(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

fof(c_0_8,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | m1_subset_1(u1_struct_0(X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ( v1_pre_topc(k6_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))) )
      & ( v2_pre_topc(k6_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))) )
      & ( l1_pre_topc(k6_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ( ~ v1_tsep_1(esk4_0,esk3_0)
      | ~ m1_pre_topc(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) )
    & ( v1_tsep_1(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) )
    & ( m1_pre_topc(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).

cnf(c_0_11,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8] :
      ( ( X7 != k8_tmap_1(X5,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))
        | X8 != u1_struct_0(X6)
        | X7 = k6_tmap_1(X5,X8)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X5)))
        | X7 = k8_tmap_1(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( esk1_3(X5,X6,X7) = u1_struct_0(X6)
        | X7 = k8_tmap_1(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( X7 != k6_tmap_1(X5,esk1_3(X5,X6,X7))
        | X7 = k8_tmap_1(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

cnf(c_0_14,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_20,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v1_tsep_1(X11,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | X12 != u1_struct_0(X11)
        | v3_pre_topc(X12,X10)
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk2_2(X10,X11),k1_zfmisc_1(u1_struct_0(X10)))
        | v1_tsep_1(X11,X10)
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X10) )
      & ( esk2_2(X10,X11) = u1_struct_0(X11)
        | v1_tsep_1(X11,X10)
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v3_pre_topc(esk2_2(X10,X11),X10)
        | v1_tsep_1(X11,X10)
        | ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_21,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k6_tmap_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_29,plain,
    ( l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_30,plain,
    ( v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_32,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_33,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk3_0)
    | v1_tsep_1(esk4_0,esk3_0)
    | k6_tmap_1(esk3_0,u1_struct_0(X1)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_36,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(X1)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk3_0)
    | ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_38,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk3_0)
    | v1_tsep_1(esk4_0,esk3_0)
    | k8_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( k8_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk3_0)
    | ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_42,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | v1_tsep_1(X1,esk3_0)
    | k8_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23])])).

cnf(c_0_44,negated_conjecture,
    ( k8_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ v1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( k8_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
