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
% DateTime   : Thu Dec  3 11:18:22 EST 2020

% Result     : Theorem 5.46s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  125 (2080 expanded)
%              Number of clauses        :   90 ( 778 expanded)
%              Number of leaves         :   17 ( 530 expanded)
%              Depth                    :   19
%              Number of atoms          :  519 (11569 expanded)
%              Number of equality atoms :   91 (1661 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(fc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_pre_topc)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | m1_subset_1(u1_pre_topc(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_19,plain,(
    ! [X41,X42] :
      ( ( u1_struct_0(k6_tmap_1(X41,X42)) = u1_struct_0(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( u1_pre_topc(k6_tmap_1(X41,X42)) = k5_tmap_1(X41,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_20,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X22,X23,X24,X25] :
      ( ( X22 = X24
        | g1_pre_topc(X22,X23) != g1_pre_topc(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) )
      & ( X23 = X25
        | g1_pre_topc(X22,X23) != g1_pre_topc(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_pre_topc(k6_tmap_1(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(k6_tmap_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | ~ v1_pre_topc(X13)
      | X13 = g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_29,plain,(
    ! [X50,X51,X52] :
      ( ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ m1_pre_topc(X51,X50)
      | ~ m1_pre_topc(X52,X51)
      | m1_pre_topc(X52,X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_30,plain,(
    ! [X43,X44] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)))
        | ~ m1_pre_topc(X44,X43)
        | ~ l1_pre_topc(X43) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),X43)
        | ~ m1_pre_topc(X44,X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

fof(c_0_31,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | l1_pre_topc(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1(esk3_0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | ~ l1_pre_topc(k6_tmap_1(esk3_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_34,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X47] :
      ( ~ l1_pre_topc(X47)
      | m1_pre_topc(X47,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k6_tmap_1(esk3_0,X2))) != g1_pre_topc(X1,X3)
    | ~ l1_pre_topc(k6_tmap_1(esk3_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k6_tmap_1(X1,X2))) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_pre_topc(k6_tmap_1(X1,X2))
    | ~ l1_pre_topc(k6_tmap_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

fof(c_0_41,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | m1_subset_1(u1_struct_0(X46),k1_zfmisc_1(u1_struct_0(X45))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_42,plain,(
    ! [X28,X29,X30,X31] :
      ( ( X30 != k8_tmap_1(X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X28)))
        | X31 != u1_struct_0(X29)
        | X30 = k6_tmap_1(X28,X31)
        | ~ v1_pre_topc(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk1_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | X30 = k8_tmap_1(X28,X29)
        | ~ v1_pre_topc(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( esk1_3(X28,X29,X30) = u1_struct_0(X29)
        | X30 = k8_tmap_1(X28,X29)
        | ~ v1_pre_topc(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( X30 != k6_tmap_1(X28,esk1_3(X28,X29,X30))
        | X30 = k8_tmap_1(X28,X29)
        | ~ v1_pre_topc(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_43,plain,(
    ! [X37,X38] :
      ( ( v1_pre_topc(k8_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( v2_pre_topc(k8_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( l1_pre_topc(k8_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_44,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_46,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))
      | m1_pre_topc(X27,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_47,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_48,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | k6_tmap_1(esk3_0,X2) != g1_pre_topc(X1,X3)
    | ~ v1_pre_topc(k6_tmap_1(esk3_0,X2))
    | ~ l1_pre_topc(k6_tmap_1(esk3_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_26]),c_0_27])]),c_0_24])).

cnf(c_0_50,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26]),c_0_27])])).

cnf(c_0_56,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | k6_tmap_1(esk3_0,u1_struct_0(X2)) != g1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(X2)))
    | ~ l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_27])])).

cnf(c_0_59,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])]),c_0_50]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_52]),c_0_26]),c_0_27])])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_34])).

cnf(c_0_62,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_27])])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_45]),c_0_27])])).

fof(c_0_65,plain,(
    ! [X21] :
      ( ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) )
      & ( v1_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).

cnf(c_0_66,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | k8_tmap_1(esk3_0,X2) != g1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ v1_pre_topc(k8_tmap_1(esk3_0,X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_26]),c_0_27])]),c_0_24]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_69,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_71,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_34])])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | k8_tmap_1(esk3_0,X2) != g1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_26]),c_0_27])]),c_0_24])).

cnf(c_0_73,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_64])]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_36]),c_0_27])])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(g1_pre_topc(X1,X3),X2)
    | ~ v1_pre_topc(g1_pre_topc(X1,X3))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_71]),c_0_37])).

cnf(c_0_76,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | k8_tmap_1(esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) != g1_pre_topc(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( k8_tmap_1(X1,g1_pre_topc(X2,X3)) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(g1_pre_topc(X2,X3),X1)
    | ~ v1_pre_topc(g1_pre_topc(X2,X3))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_71]),c_0_37])).

cnf(c_0_79,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_45])).

fof(c_0_80,plain,(
    ! [X39,X40] :
      ( ( ~ r2_hidden(X40,u1_pre_topc(X39))
        | u1_pre_topc(X39) = k5_tmap_1(X39,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( u1_pre_topc(X39) != k5_tmap_1(X39,X40)
        | r2_hidden(X40,u1_pre_topc(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_73]),c_0_27])])).

cnf(c_0_82,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | v1_tsep_1(esk4_0,esk3_0)
    | k8_tmap_1(esk3_0,esk4_0) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_76]),c_0_27])])).

cnf(c_0_84,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_45])).

cnf(c_0_85,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | v1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_76]),c_0_27])]),c_0_24])).

fof(c_0_86,plain,(
    ! [X14,X15] :
      ( ( ~ v3_pre_topc(X15,X14)
        | r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(X15,u1_pre_topc(X14))
        | v3_pre_topc(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_87,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v1_tsep_1(X34,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | X35 != u1_struct_0(X34)
        | v3_pre_topc(X35,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk2_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))
        | v1_tsep_1(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( esk2_2(X33,X34) = u1_struct_0(X34)
        | v1_tsep_1(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ v3_pre_topc(esk2_2(X33,X34),X33)
        | v1_tsep_1(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) != g1_pre_topc(X1,X2)
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_26]),c_0_73]),c_0_27])]),c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_78]),c_0_26]),c_0_73]),c_0_27])]),c_0_24])).

cnf(c_0_90,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_69]),c_0_64])]),c_0_70])).

cnf(c_0_92,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_93,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_21])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_34])]),c_0_84])]),c_0_85])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_96,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) != g1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_69]),c_0_64])]),c_0_70])).

cnf(c_0_98,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_69]),c_0_64])]),c_0_70])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))
    | k5_tmap_1(esk3_0,u1_struct_0(esk4_0)) != u1_pre_topc(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_26]),c_0_27])]),c_0_24])).

cnf(c_0_100,plain,
    ( k5_tmap_1(X1,u1_struct_0(X2)) = u1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_59]),c_0_50])).

cnf(c_0_101,negated_conjecture,
    ( u1_pre_topc(esk3_0) = X1
    | v1_tsep_1(esk4_0,esk3_0)
    | k8_tmap_1(esk3_0,esk4_0) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_76]),c_0_27])])).

cnf(c_0_102,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))) = k8_tmap_1(esk3_0,esk4_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_94]),c_0_84])]),c_0_85])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_91]),c_0_27])])).

cnf(c_0_104,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_96]),c_0_50])).

cnf(c_0_105,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X2)),k5_tmap_1(X1,X2)) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_pre_topc(k6_tmap_1(X1,X2))
    | ~ l1_pre_topc(k6_tmap_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_92])).

cnf(c_0_106,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk3_0)
    | ~ v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_34])]),c_0_98])])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))
    | u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) != u1_pre_topc(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_26]),c_0_45]),c_0_27])]),c_0_24])).

cnf(c_0_108,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) = u1_pre_topc(esk3_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))
    | ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_45]),c_0_27])])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_111,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),k5_tmap_1(esk3_0,u1_struct_0(esk4_0))) = k6_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | ~ v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_26]),c_0_98]),c_0_27]),c_0_91])]),c_0_24])).

cnf(c_0_112,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_45])])).

cnf(c_0_115,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k6_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | ~ v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_26]),c_0_27]),c_0_113]),c_0_91])]),c_0_24])).

cnf(c_0_116,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_117,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_118,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ v1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_59]),c_0_26]),c_0_45]),c_0_27])]),c_0_24])).

cnf(c_0_120,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_121,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_122,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_53]),c_0_26]),c_0_45]),c_0_27])]),c_0_24])).

cnf(c_0_123,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_50])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_45]),c_0_27]),c_0_113])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.46/5.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 5.46/5.66  # and selection function PSelectUnlessUniqMaxPos.
% 5.46/5.66  #
% 5.46/5.66  # Preprocessing time       : 0.029 s
% 5.46/5.66  # Presaturation interreduction done
% 5.46/5.66  
% 5.46/5.66  # Proof found!
% 5.46/5.66  # SZS status Theorem
% 5.46/5.66  # SZS output start CNFRefutation
% 5.46/5.66  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 5.46/5.66  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.46/5.66  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 5.46/5.66  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 5.46/5.66  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.46/5.66  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 5.46/5.66  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 5.46/5.66  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.46/5.66  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.46/5.66  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.46/5.66  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 5.46/5.66  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 5.46/5.66  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.46/5.66  fof(fc7_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>(~(v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))&v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_pre_topc)).
% 5.46/5.66  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 5.46/5.66  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.46/5.66  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 5.46/5.66  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 5.46/5.66  fof(c_0_18, plain, ![X19]:(~l1_pre_topc(X19)|m1_subset_1(u1_pre_topc(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 5.46/5.66  fof(c_0_19, plain, ![X41, X42]:((u1_struct_0(k6_tmap_1(X41,X42))=u1_struct_0(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(u1_pre_topc(k6_tmap_1(X41,X42))=k5_tmap_1(X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 5.46/5.66  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0))&((v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0))&(m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).
% 5.46/5.66  cnf(c_0_21, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.46/5.66  cnf(c_0_22, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.46/5.66  fof(c_0_23, plain, ![X22, X23, X24, X25]:((X22=X24|g1_pre_topc(X22,X23)!=g1_pre_topc(X24,X25)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))))&(X23=X25|g1_pre_topc(X22,X23)!=g1_pre_topc(X24,X25)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 5.46/5.66  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.46/5.66  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(u1_pre_topc(k6_tmap_1(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(k6_tmap_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 5.46/5.66  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.46/5.66  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.46/5.66  fof(c_0_28, plain, ![X13]:(~l1_pre_topc(X13)|(~v1_pre_topc(X13)|X13=g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 5.46/5.66  fof(c_0_29, plain, ![X50, X51, X52]:(~v2_pre_topc(X50)|~l1_pre_topc(X50)|(~m1_pre_topc(X51,X50)|(~m1_pre_topc(X52,X51)|m1_pre_topc(X52,X50)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 5.46/5.66  fof(c_0_30, plain, ![X43, X44]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)))|~m1_pre_topc(X44,X43)|~l1_pre_topc(X43))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),X43)|~m1_pre_topc(X44,X43)|~l1_pre_topc(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 5.46/5.66  fof(c_0_31, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|l1_pre_topc(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 5.46/5.66  cnf(c_0_32, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.46/5.66  cnf(c_0_33, negated_conjecture, (m1_subset_1(u1_pre_topc(k6_tmap_1(esk3_0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))|~l1_pre_topc(k6_tmap_1(esk3_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 5.46/5.66  cnf(c_0_34, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 5.46/5.66  cnf(c_0_35, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.46/5.66  cnf(c_0_36, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.46/5.66  cnf(c_0_37, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.46/5.66  fof(c_0_38, plain, ![X47]:(~l1_pre_topc(X47)|m1_pre_topc(X47,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 5.46/5.66  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk3_0)=X1|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k6_tmap_1(esk3_0,X2)))!=g1_pre_topc(X1,X3)|~l1_pre_topc(k6_tmap_1(esk3_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.46/5.66  cnf(c_0_40, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k6_tmap_1(X1,X2)))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_pre_topc(k6_tmap_1(X1,X2))|~l1_pre_topc(k6_tmap_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 5.46/5.66  fof(c_0_41, plain, ![X45, X46]:(~l1_pre_topc(X45)|(~m1_pre_topc(X46,X45)|m1_subset_1(u1_struct_0(X46),k1_zfmisc_1(u1_struct_0(X45))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 5.46/5.66  fof(c_0_42, plain, ![X28, X29, X30, X31]:((X30!=k8_tmap_1(X28,X29)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X28)))|(X31!=u1_struct_0(X29)|X30=k6_tmap_1(X28,X31)))|(~v1_pre_topc(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|~m1_pre_topc(X29,X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&((m1_subset_1(esk1_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))|X30=k8_tmap_1(X28,X29)|(~v1_pre_topc(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|~m1_pre_topc(X29,X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&((esk1_3(X28,X29,X30)=u1_struct_0(X29)|X30=k8_tmap_1(X28,X29)|(~v1_pre_topc(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|~m1_pre_topc(X29,X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(X30!=k6_tmap_1(X28,esk1_3(X28,X29,X30))|X30=k8_tmap_1(X28,X29)|(~v1_pre_topc(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|~m1_pre_topc(X29,X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 5.46/5.66  fof(c_0_43, plain, ![X37, X38]:(((v1_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))&(v2_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37))))&(l1_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 5.46/5.66  cnf(c_0_44, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v2_pre_topc(X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 5.46/5.66  cnf(c_0_45, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.46/5.66  fof(c_0_46, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_pre_topc(X27,g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))|m1_pre_topc(X27,X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 5.46/5.66  cnf(c_0_47, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 5.46/5.66  cnf(c_0_48, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 5.46/5.66  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk3_0)=X1|k6_tmap_1(esk3_0,X2)!=g1_pre_topc(X1,X3)|~v1_pre_topc(k6_tmap_1(esk3_0,X2))|~l1_pre_topc(k6_tmap_1(esk3_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_26]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_50, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.46/5.66  cnf(c_0_51, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.46/5.66  cnf(c_0_52, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.46/5.66  cnf(c_0_53, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.46/5.66  cnf(c_0_54, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.46/5.66  cnf(c_0_55, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26]), c_0_27])])).
% 5.46/5.66  cnf(c_0_56, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 5.46/5.66  cnf(c_0_57, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 5.46/5.66  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk3_0)=X1|k6_tmap_1(esk3_0,u1_struct_0(X2))!=g1_pre_topc(X1,X3)|~m1_pre_topc(X2,esk3_0)|~v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(X2)))|~l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_27])])).
% 5.46/5.66  cnf(c_0_59, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])]), c_0_50]), c_0_52]), c_0_53]), c_0_54])).
% 5.46/5.66  cnf(c_0_60, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_52]), c_0_26]), c_0_27])])).
% 5.46/5.66  cnf(c_0_61, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)|~v1_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_55, c_0_34])).
% 5.46/5.66  cnf(c_0_62, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_57])).
% 5.46/5.66  cnf(c_0_63, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_27])])).
% 5.46/5.66  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_45]), c_0_27])])).
% 5.46/5.66  fof(c_0_65, plain, ![X21]:((~v2_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|(v2_struct_0(X21)|~l1_pre_topc(X21)))&(v1_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|(v2_struct_0(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).
% 5.46/5.66  cnf(c_0_66, plain, (u1_struct_0(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 5.46/5.66  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk3_0)=X1|k8_tmap_1(esk3_0,X2)!=g1_pre_topc(X1,X3)|~m1_pre_topc(X2,esk3_0)|~v1_pre_topc(k8_tmap_1(esk3_0,X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_26]), c_0_27])]), c_0_24]), c_0_60])).
% 5.46/5.66  cnf(c_0_68, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)|~v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 5.46/5.66  cnf(c_0_69, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 5.46/5.66  cnf(c_0_70, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.46/5.66  cnf(c_0_71, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X1|~v1_pre_topc(g1_pre_topc(X1,X2))|~l1_pre_topc(g1_pre_topc(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_34])])).
% 5.46/5.66  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk3_0)=X1|k8_tmap_1(esk3_0,X2)!=g1_pre_topc(X1,X3)|~m1_pre_topc(X2,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_53]), c_0_26]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_73, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_64])]), c_0_70])).
% 5.46/5.66  cnf(c_0_74, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_36]), c_0_27])])).
% 5.46/5.66  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(g1_pre_topc(X1,X3),X2)|~v1_pre_topc(g1_pre_topc(X1,X3))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_71]), c_0_37])).
% 5.46/5.66  cnf(c_0_76, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.46/5.66  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk3_0)=X1|k8_tmap_1(esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))!=g1_pre_topc(X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 5.46/5.66  cnf(c_0_78, plain, (k8_tmap_1(X1,g1_pre_topc(X2,X3))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(g1_pre_topc(X2,X3),X1)|~v1_pre_topc(g1_pre_topc(X2,X3))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_71]), c_0_37])).
% 5.46/5.66  cnf(c_0_79, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(spm,[status(thm)],[c_0_74, c_0_45])).
% 5.46/5.66  fof(c_0_80, plain, ![X39, X40]:((~r2_hidden(X40,u1_pre_topc(X39))|u1_pre_topc(X39)=k5_tmap_1(X39,X40)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(u1_pre_topc(X39)!=k5_tmap_1(X39,X40)|r2_hidden(X40,u1_pre_topc(X39))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 5.46/5.66  cnf(c_0_81, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_73]), c_0_27])])).
% 5.46/5.66  cnf(c_0_82, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.46/5.66  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk3_0)=X1|v1_tsep_1(esk4_0,esk3_0)|k8_tmap_1(esk3_0,esk4_0)!=g1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_76]), c_0_27])])).
% 5.46/5.66  cnf(c_0_84, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_45])).
% 5.46/5.66  cnf(c_0_85, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|v1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_76]), c_0_27])]), c_0_24])).
% 5.46/5.66  fof(c_0_86, plain, ![X14, X15]:((~v3_pre_topc(X15,X14)|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~r2_hidden(X15,u1_pre_topc(X14))|v3_pre_topc(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 5.46/5.66  fof(c_0_87, plain, ![X33, X34, X35]:((~v1_tsep_1(X34,X33)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|(X35!=u1_struct_0(X34)|v3_pre_topc(X35,X33)))|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&((m1_subset_1(esk2_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))|v1_tsep_1(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&((esk2_2(X33,X34)=u1_struct_0(X34)|v1_tsep_1(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&(~v3_pre_topc(esk2_2(X33,X34),X33)|v1_tsep_1(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 5.46/5.66  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk3_0)=X1|k6_tmap_1(esk3_0,u1_struct_0(esk4_0))!=g1_pre_topc(X1,X2)|~v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_26]), c_0_73]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_89, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))|~v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_78]), c_0_26]), c_0_73]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_90, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 5.46/5.66  cnf(c_0_91, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_69]), c_0_64])]), c_0_70])).
% 5.46/5.66  cnf(c_0_92, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.46/5.66  cnf(c_0_93, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_82, c_0_21])).
% 5.46/5.66  cnf(c_0_94, negated_conjecture, (u1_struct_0(k8_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk3_0)|v1_tsep_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_34])]), c_0_84])]), c_0_85])).
% 5.46/5.66  cnf(c_0_95, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 5.46/5.66  cnf(c_0_96, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 5.46/5.66  cnf(c_0_97, negated_conjecture, (u1_struct_0(esk3_0)=X1|k6_tmap_1(esk3_0,u1_struct_0(esk4_0))!=g1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_69]), c_0_64])]), c_0_70])).
% 5.46/5.66  cnf(c_0_98, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_69]), c_0_64])]), c_0_70])).
% 5.46/5.66  cnf(c_0_99, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))|k5_tmap_1(esk3_0,u1_struct_0(esk4_0))!=u1_pre_topc(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_26]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_100, plain, (k5_tmap_1(X1,u1_struct_0(X2))=u1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_59]), c_0_50])).
% 5.46/5.66  cnf(c_0_101, negated_conjecture, (u1_pre_topc(esk3_0)=X1|v1_tsep_1(esk4_0,esk3_0)|k8_tmap_1(esk3_0,esk4_0)!=g1_pre_topc(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_76]), c_0_27])])).
% 5.46/5.66  cnf(c_0_102, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)))=k8_tmap_1(esk3_0,esk4_0)|v1_tsep_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_94]), c_0_84])]), c_0_85])).
% 5.46/5.66  cnf(c_0_103, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_91]), c_0_27])])).
% 5.46/5.66  cnf(c_0_104, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_96]), c_0_50])).
% 5.46/5.66  cnf(c_0_105, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X2)),k5_tmap_1(X1,X2))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_pre_topc(k6_tmap_1(X1,X2))|~l1_pre_topc(k6_tmap_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_92])).
% 5.46/5.66  cnf(c_0_106, negated_conjecture, (u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))=u1_struct_0(esk3_0)|~v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_34])]), c_0_98])])).
% 5.46/5.66  cnf(c_0_107, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))|u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))!=u1_pre_topc(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_26]), c_0_45]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_108, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))=u1_pre_topc(esk3_0)|v1_tsep_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 5.46/5.66  cnf(c_0_109, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))|~v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_45]), c_0_27])])).
% 5.46/5.66  cnf(c_0_110, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.46/5.66  cnf(c_0_111, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),k5_tmap_1(esk3_0,u1_struct_0(esk4_0)))=k6_tmap_1(esk3_0,u1_struct_0(esk4_0))|~v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_26]), c_0_98]), c_0_27]), c_0_91])]), c_0_24])).
% 5.46/5.66  cnf(c_0_112, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 5.46/5.66  cnf(c_0_113, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 5.46/5.66  cnf(c_0_114, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_45])])).
% 5.46/5.66  cnf(c_0_115, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k6_tmap_1(esk3_0,u1_struct_0(esk4_0))|~v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_26]), c_0_27]), c_0_113]), c_0_91])]), c_0_24])).
% 5.46/5.66  cnf(c_0_116, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)|~v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 5.46/5.66  cnf(c_0_117, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 5.46/5.66  cnf(c_0_118, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 5.46/5.66  cnf(c_0_119, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)|~v1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_59]), c_0_26]), c_0_45]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_120, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 5.46/5.66  cnf(c_0_121, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 5.46/5.66  cnf(c_0_122, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_53]), c_0_26]), c_0_45]), c_0_27])]), c_0_24])).
% 5.46/5.66  cnf(c_0_123, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_50])).
% 5.46/5.66  cnf(c_0_124, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_45]), c_0_27]), c_0_113])]), ['proof']).
% 5.46/5.66  # SZS output end CNFRefutation
% 5.46/5.66  # Proof object total steps             : 125
% 5.46/5.66  # Proof object clause steps            : 90
% 5.46/5.66  # Proof object formula steps           : 35
% 5.46/5.66  # Proof object conjectures             : 52
% 5.46/5.66  # Proof object clause conjectures      : 49
% 5.46/5.66  # Proof object formula conjectures     : 3
% 5.46/5.66  # Proof object initial clauses used    : 31
% 5.46/5.66  # Proof object initial formulas used   : 17
% 5.46/5.66  # Proof object generating inferences   : 56
% 5.46/5.66  # Proof object simplifying inferences  : 132
% 5.46/5.66  # Training examples: 0 positive, 0 negative
% 5.46/5.66  # Parsed axioms                        : 24
% 5.46/5.66  # Removed by relevancy pruning/SinE    : 0
% 5.46/5.66  # Initial clauses                      : 49
% 5.46/5.66  # Removed in clause preprocessing      : 0
% 5.46/5.66  # Initial clauses in saturation        : 49
% 5.46/5.66  # Processed clauses                    : 13882
% 5.46/5.66  # ...of these trivial                  : 623
% 5.46/5.66  # ...subsumed                          : 8516
% 5.46/5.66  # ...remaining for further processing  : 4743
% 5.46/5.66  # Other redundant clauses eliminated   : 7908
% 5.46/5.66  # Clauses deleted for lack of memory   : 0
% 5.46/5.66  # Backward-subsumed                    : 1338
% 5.46/5.66  # Backward-rewritten                   : 354
% 5.46/5.66  # Generated clauses                    : 376866
% 5.46/5.66  # ...of the previous two non-trivial   : 351111
% 5.46/5.66  # Contextual simplify-reflections      : 492
% 5.46/5.66  # Paramodulations                      : 368768
% 5.46/5.66  # Factorizations                       : 26
% 5.46/5.66  # Equation resolutions                 : 7969
% 5.46/5.66  # Propositional unsat checks           : 0
% 5.46/5.66  #    Propositional check models        : 0
% 5.46/5.66  #    Propositional check unsatisfiable : 0
% 5.46/5.66  #    Propositional clauses             : 0
% 5.46/5.66  #    Propositional clauses after purity: 0
% 5.46/5.66  #    Propositional unsat core size     : 0
% 5.46/5.66  #    Propositional preprocessing time  : 0.000
% 5.46/5.66  #    Propositional encoding time       : 0.000
% 5.46/5.66  #    Propositional solver time         : 0.000
% 5.46/5.66  #    Success case prop preproc time    : 0.000
% 5.46/5.66  #    Success case prop encoding time   : 0.000
% 5.46/5.66  #    Success case prop solver time     : 0.000
% 5.46/5.66  # Current number of processed clauses  : 2899
% 5.46/5.66  #    Positive orientable unit clauses  : 95
% 5.46/5.66  #    Positive unorientable unit clauses: 0
% 5.46/5.66  #    Negative unit clauses             : 3
% 5.46/5.66  #    Non-unit-clauses                  : 2801
% 5.46/5.66  # Current number of unprocessed clauses: 336360
% 5.46/5.66  # ...number of literals in the above   : 3683853
% 5.46/5.66  # Current number of archived formulas  : 0
% 5.46/5.66  # Current number of archived clauses   : 1842
% 5.46/5.66  # Clause-clause subsumption calls (NU) : 1872331
% 5.46/5.66  # Rec. Clause-clause subsumption calls : 388874
% 5.46/5.66  # Non-unit clause-clause subsumptions  : 10023
% 5.46/5.66  # Unit Clause-clause subsumption calls : 28151
% 5.46/5.66  # Rewrite failures with RHS unbound    : 0
% 5.46/5.66  # BW rewrite match attempts            : 2644
% 5.46/5.66  # BW rewrite match successes           : 57
% 5.46/5.66  # Condensation attempts                : 0
% 5.46/5.66  # Condensation successes               : 0
% 5.46/5.66  # Termbank termtop insertions          : 12345462
% 5.46/5.68  
% 5.46/5.68  # -------------------------------------------------
% 5.46/5.68  # User time                : 5.148 s
% 5.46/5.68  # System time              : 0.188 s
% 5.46/5.68  # Total time               : 5.336 s
% 5.46/5.68  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
