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
% DateTime   : Thu Dec  3 11:18:22 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  211 (29672 expanded)
%              Number of clauses        :  154 (11257 expanded)
%              Number of leaves         :   28 (7400 expanded)
%              Depth                    :   32
%              Number of atoms          :  827 (163945 expanded)
%              Number of equality atoms :   89 (20686 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t12_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(t58_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

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

fof(t19_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tsep_1(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
               => ( v1_tsep_1(X2,X3)
                  & m1_pre_topc(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

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

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_28,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_29,plain,(
    ! [X56,X57] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)))
        | ~ m1_pre_topc(X57,X56)
        | ~ l1_pre_topc(X56) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)),X56)
        | ~ m1_pre_topc(X57,X56)
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

fof(c_0_30,plain,(
    ! [X58,X59,X60] :
      ( ( ~ m1_pre_topc(X59,X58)
        | m1_pre_topc(X60,X58)
        | X59 != g1_pre_topc(u1_struct_0(X60),u1_pre_topc(X60))
        | ~ v2_pre_topc(X60)
        | ~ l1_pre_topc(X60)
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | ~ l1_pre_topc(X58) )
      & ( ~ m1_pre_topc(X60,X58)
        | m1_pre_topc(X59,X58)
        | X59 != g1_pre_topc(u1_struct_0(X60),u1_pre_topc(X60))
        | ~ v2_pre_topc(X60)
        | ~ l1_pre_topc(X60)
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | ~ l1_pre_topc(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

fof(c_0_31,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))
      | v2_pre_topc(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).

cnf(c_0_32,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X66] :
      ( ~ l1_pre_topc(X66)
      | m1_pre_topc(X66,X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_35,plain,(
    ! [X17,X18] :
      ( ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | v2_pre_topc(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_36,negated_conjecture,(
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

fof(c_0_37,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])])).

fof(c_0_44,plain,(
    ! [X67,X68,X69] :
      ( ( ~ r1_tarski(u1_struct_0(X68),u1_struct_0(X69))
        | m1_pre_topc(X68,X69)
        | ~ m1_pre_topc(X69,X67)
        | ~ m1_pre_topc(X68,X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) )
      & ( ~ m1_pre_topc(X68,X69)
        | r1_tarski(u1_struct_0(X68),u1_struct_0(X69))
        | ~ m1_pre_topc(X69,X67)
        | ~ m1_pre_topc(X68,X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X31,X32] :
      ( ( ~ m1_pre_topc(X31,X32)
        | m1_pre_topc(X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))
        | ~ l1_pre_topc(X32)
        | ~ l1_pre_topc(X31) )
      & ( ~ m1_pre_topc(X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))
        | m1_pre_topc(X31,X32)
        | ~ l1_pre_topc(X32)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_38,c_0_32])]),c_0_39])).

cnf(c_0_48,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

fof(c_0_55,plain,(
    ! [X44,X45] :
      ( ( v1_pre_topc(k8_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_pre_topc(X45,X44) )
      & ( v2_pre_topc(k8_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_pre_topc(X45,X44) )
      & ( l1_pre_topc(k8_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_pre_topc(X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_56,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_50]),c_0_52])])).

fof(c_0_60,plain,(
    ! [X53,X54,X55] :
      ( ( u1_struct_0(k8_tmap_1(X53,X54)) = u1_struct_0(X53)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X53)
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) )
      & ( ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))
        | X55 != u1_struct_0(X54)
        | u1_pre_topc(k8_tmap_1(X53,X54)) = k5_tmap_1(X53,X55)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X53)
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

cnf(c_0_61,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_63,plain,(
    ! [X70,X71,X72] :
      ( ~ v2_pre_topc(X70)
      | ~ l1_pre_topc(X70)
      | ~ m1_pre_topc(X71,X70)
      | ~ m1_pre_topc(X72,X71)
      | m1_pre_topc(X72,X70) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_64,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_65,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_50]),c_0_52])])).

fof(c_0_68,plain,(
    ! [X64,X65] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_pre_topc(X65,X64)
      | m1_subset_1(u1_struct_0(X65),k1_zfmisc_1(u1_struct_0(X64))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_69,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_71,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k8_tmap_1(X1,X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_41])).

cnf(c_0_74,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_75,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_64,c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_59])])).

fof(c_0_78,plain,(
    ! [X46,X47] :
      ( ( ~ r2_hidden(X47,u1_pre_topc(X46))
        | u1_pre_topc(X46) = k5_tmap_1(X46,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( u1_pre_topc(X46) != k5_tmap_1(X46,X47)
        | r2_hidden(X47,u1_pre_topc(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_79,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk4_0,esk4_0)) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_59])]),c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_71]),c_0_59])]),c_0_72])).

cnf(c_0_82,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_83,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_77]),c_0_71]),c_0_59])])).

cnf(c_0_86,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_88,plain,
    ( k5_tmap_1(X1,u1_struct_0(X2)) = u1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]),c_0_79])).

cnf(c_0_89,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_91,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_41])).

cnf(c_0_92,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_58]),c_0_67]),c_0_59])])).

cnf(c_0_93,plain,
    ( v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_76]),c_0_48])).

cnf(c_0_94,negated_conjecture,
    ( k5_tmap_1(esk4_0,u1_struct_0(X1)) = u1_pre_topc(esk4_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk4_0,esk4_0))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_71]),c_0_59])]),c_0_72])).

cnf(c_0_95,negated_conjecture,
    ( k5_tmap_1(esk4_0,u1_struct_0(esk4_0)) = u1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_70]),c_0_71]),c_0_59])]),c_0_72])).

fof(c_0_96,plain,(
    ! [X10] : m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_97,plain,(
    ! [X9] : k2_subset_1(X9) = X9 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_98,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_80])).

cnf(c_0_100,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_92]),c_0_67])])).

cnf(c_0_101,negated_conjecture,
    ( v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_58]),c_0_59])])).

cnf(c_0_102,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) = u1_pre_topc(esk4_0)
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),k8_tmap_1(esk4_0,esk4_0))
    | ~ r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_80]),c_0_95])).

fof(c_0_103,plain,(
    ! [X19,X20] :
      ( ( ~ v3_pre_topc(X20,X19)
        | r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(X20,u1_pre_topc(X19))
        | v3_pre_topc(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_104,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_105,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_106,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_107,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_33]),c_0_32])).

cnf(c_0_108,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_101])).

fof(c_0_109,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | ~ v1_pre_topc(X16)
      | X16 = g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_110,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_111,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) = u1_pre_topc(esk4_0)
    | ~ r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_41]),c_0_81])])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_113,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_114,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k8_tmap_1(X1,X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_41])).

cnf(c_0_115,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_116,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_92]),c_0_77])])).

cnf(c_0_117,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_50]),c_0_52])])).

cnf(c_0_119,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) = u1_pre_topc(esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_59]),c_0_113])])).

cnf(c_0_120,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_71]),c_0_59])]),c_0_72])).

fof(c_0_121,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_tsep_1(X39,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | X40 != u1_struct_0(X39)
        | v3_pre_topc(X40,X38)
        | ~ m1_pre_topc(X39,X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk2_2(X38,X39),k1_zfmisc_1(u1_struct_0(X38)))
        | v1_tsep_1(X39,X38)
        | ~ m1_pre_topc(X39,X38)
        | ~ l1_pre_topc(X38) )
      & ( esk2_2(X38,X39) = u1_struct_0(X39)
        | v1_tsep_1(X39,X38)
        | ~ m1_pre_topc(X39,X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ v3_pre_topc(esk2_2(X38,X39),X38)
        | v1_tsep_1(X39,X38)
        | ~ m1_pre_topc(X39,X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_122,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_123,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_124,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),esk3_0)
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_77])])).

cnf(c_0_125,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_116]),c_0_118]),c_0_67])])).

cnf(c_0_126,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k8_tmap_1(esk4_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_119]),c_0_80]),c_0_120]),c_0_81])])).

cnf(c_0_127,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

fof(c_0_128,plain,(
    ! [X61,X62,X63] :
      ( ( v1_tsep_1(X62,X63)
        | ~ r1_tarski(u1_struct_0(X62),u1_struct_0(X63))
        | v2_struct_0(X63)
        | ~ m1_pre_topc(X63,X61)
        | ~ v1_tsep_1(X62,X61)
        | ~ m1_pre_topc(X62,X61)
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( m1_pre_topc(X62,X63)
        | ~ r1_tarski(u1_struct_0(X62),u1_struct_0(X63))
        | v2_struct_0(X63)
        | ~ m1_pre_topc(X63,X61)
        | ~ v1_tsep_1(X62,X61)
        | ~ m1_pre_topc(X62,X61)
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_tsep_1])])])])])).

cnf(c_0_129,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_122]),c_0_52])])).

cnf(c_0_130,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_51]),c_0_52])]),c_0_123])).

cnf(c_0_131,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_122]),c_0_52])])).

cnf(c_0_132,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_133,negated_conjecture,
    ( m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_126])).

cnf(c_0_134,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_127]),c_0_79])).

cnf(c_0_135,plain,
    ( v1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ v1_tsep_1(X1,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_136,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_33]),c_0_130])])).

cnf(c_0_137,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(esk4_0,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_50])).

cnf(c_0_138,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_132]),c_0_51]),c_0_52]),c_0_59])])).

cnf(c_0_139,negated_conjecture,
    ( m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)
    | ~ v1_tsep_1(esk4_0,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_70]),c_0_59])])).

cnf(c_0_140,negated_conjecture,
    ( v1_tsep_1(X1,esk4_0)
    | v2_struct_0(X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_90]),c_0_72]),c_0_75])).

cnf(c_0_141,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_67]),c_0_137])).

fof(c_0_142,plain,(
    ! [X27,X28,X29] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_143,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ v1_tsep_1(esk4_0,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_70]),c_0_59])])).

cnf(c_0_144,negated_conjecture,
    ( v1_tsep_1(X1,esk4_0)
    | ~ v1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_50]),c_0_51]),c_0_52])]),c_0_123])).

cnf(c_0_145,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_141]),c_0_51]),c_0_52]),c_0_59])])).

cnf(c_0_146,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_147,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_70])]),c_0_145])).

cnf(c_0_148,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_41])).

cnf(c_0_149,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_79]),c_0_32])).

cnf(c_0_150,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_67]),c_0_59])])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_52])])).

cnf(c_0_152,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_151,c_0_66])).

cnf(c_0_153,negated_conjecture,
    ( k5_tmap_1(esk3_0,u1_struct_0(esk4_0)) = u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_50]),c_0_51]),c_0_52])]),c_0_123]),c_0_72])).

cnf(c_0_154,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) = u1_pre_topc(esk3_0)
    | ~ r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_152]),c_0_153]),c_0_51]),c_0_52])]),c_0_123])).

cnf(c_0_155,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_156,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_157,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) = u1_pre_topc(esk3_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_112]),c_0_52]),c_0_152])])).

cnf(c_0_158,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_51]),c_0_52])]),c_0_72]),c_0_123])).

cnf(c_0_159,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_50]),c_0_51]),c_0_52])]),c_0_123])).

cnf(c_0_160,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_161,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = u1_struct_0(esk4_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_50]),c_0_52])])).

cnf(c_0_162,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_163,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_50])])).

cnf(c_0_164,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_157]),c_0_158]),c_0_159]),c_0_130])])).

cnf(c_0_165,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_50]),c_0_52])])).

fof(c_0_166,plain,(
    ! [X50,X51,X52] :
      ( v2_struct_0(X50)
      | ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X50,X51))))
      | X52 != X51
      | v3_pre_topc(X52,k6_tmap_1(X50,X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

fof(c_0_167,plain,(
    ! [X48,X49] :
      ( ( u1_struct_0(k6_tmap_1(X48,X49)) = u1_struct_0(X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( u1_pre_topc(k6_tmap_1(X48,X49)) = k5_tmap_1(X48,X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_168,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_76]),c_0_48])).

cnf(c_0_169,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_158]),c_0_159]),c_0_130])])).

cnf(c_0_170,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_50]),c_0_51]),c_0_52])]),c_0_123])).

cnf(c_0_171,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_165])).

fof(c_0_172,plain,(
    ! [X33,X34,X35,X36] :
      ( ( X35 != k8_tmap_1(X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))
        | X36 != u1_struct_0(X34)
        | X35 = k6_tmap_1(X33,X36)
        | ~ v1_pre_topc(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk1_3(X33,X34,X35),k1_zfmisc_1(u1_struct_0(X33)))
        | X35 = k8_tmap_1(X33,X34)
        | ~ v1_pre_topc(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( esk1_3(X33,X34,X35) = u1_struct_0(X34)
        | X35 = k8_tmap_1(X33,X34)
        | ~ v1_pre_topc(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( X35 != k6_tmap_1(X33,esk1_3(X33,X34,X35))
        | X35 = k8_tmap_1(X33,X34)
        | ~ v1_pre_topc(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

cnf(c_0_173,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(esk3_0,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_41]),c_0_52])])).

cnf(c_0_174,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_166])).

cnf(c_0_175,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_167])).

cnf(c_0_176,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_158]),c_0_130])])).

cnf(c_0_177,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_158]),c_0_169]),c_0_170]),c_0_130])])).

cnf(c_0_178,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_141])).

cnf(c_0_179,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_134]),c_0_50]),c_0_52])])).

cnf(c_0_180,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_172])).

cnf(c_0_181,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_173]),c_0_170]),c_0_130])])).

cnf(c_0_182,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_174])).

cnf(c_0_183,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(X1))) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_176]),c_0_51]),c_0_52])]),c_0_123])).

cnf(c_0_184,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_177])).

cnf(c_0_185,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[c_0_178,c_0_179])).

cnf(c_0_186,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_180])]),c_0_79]),c_0_62]),c_0_106]),c_0_162])).

fof(c_0_187,plain,(
    ! [X24] :
      ( ~ v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | v1_xboole_0(u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_188,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_189,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_181,c_0_50])).

cnf(c_0_190,negated_conjecture,
    ( esk2_2(k8_tmap_1(esk3_0,esk4_0),esk4_0) = u1_struct_0(esk4_0)
    | v1_tsep_1(esk4_0,k8_tmap_1(esk3_0,esk4_0))
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_137]),c_0_130])])).

cnf(c_0_191,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),k6_tmap_1(esk3_0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_183]),c_0_51]),c_0_52])]),c_0_123]),c_0_176])).

cnf(c_0_192,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_185]),c_0_77]),c_0_66])])).

cnf(c_0_193,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_50]),c_0_51]),c_0_52])]),c_0_123])).

cnf(c_0_194,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_187])).

cnf(c_0_195,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_188])).

cnf(c_0_196,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_189,c_0_179])).

cnf(c_0_197,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_50])).

cnf(c_0_198,negated_conjecture,
    ( v1_tsep_1(esk4_0,k8_tmap_1(esk3_0,esk4_0))
    | v1_tsep_1(esk4_0,esk3_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_190]),c_0_130])]),c_0_137])).

cnf(c_0_199,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_192]),c_0_193]),c_0_185])])).

fof(c_0_200,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ v1_xboole_0(u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_201,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_194,c_0_195])).

cnf(c_0_202,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_196]),c_0_179]),c_0_123]),c_0_197])).

cnf(c_0_203,negated_conjecture,
    ( v1_tsep_1(esk4_0,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_198,c_0_199])]),c_0_179])).

cnf(c_0_204,negated_conjecture,
    ( m1_pre_topc(esk3_0,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[c_0_173,c_0_179])).

cnf(c_0_205,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_200])).

cnf(c_0_206,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_158]),c_0_130])])).

cnf(c_0_207,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_203]),c_0_204]),c_0_170]),c_0_130])])).

cnf(c_0_208,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_205,c_0_195])).

cnf(c_0_209,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_206,c_0_207])])).

cnf(c_0_210,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_209]),c_0_52])]),c_0_123]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:33:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.64/0.83  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.64/0.83  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.64/0.83  #
% 0.64/0.83  # Preprocessing time       : 0.032 s
% 0.64/0.83  # Presaturation interreduction done
% 0.64/0.83  
% 0.64/0.83  # Proof found!
% 0.64/0.83  # SZS status Theorem
% 0.64/0.83  # SZS output start CNFRefutation
% 0.64/0.83  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.64/0.83  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.64/0.83  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.64/0.83  fof(t58_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_pre_topc)).
% 0.64/0.83  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.64/0.83  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.64/0.83  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 0.64/0.83  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.64/0.83  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.64/0.83  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.64/0.83  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.64/0.83  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.64/0.83  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.64/0.83  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.64/0.83  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.64/0.83  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.64/0.83  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.64/0.83  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.64/0.83  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.64/0.83  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.64/0.83  fof(t19_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))=>(v1_tsep_1(X2,X3)&m1_pre_topc(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 0.64/0.83  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.64/0.83  fof(t105_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))=>(X3=X2=>v3_pre_topc(X3,k6_tmap_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 0.64/0.83  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.64/0.83  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.64/0.83  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.64/0.83  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.64/0.83  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.64/0.83  fof(c_0_28, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.64/0.83  fof(c_0_29, plain, ![X56, X57]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)))|~m1_pre_topc(X57,X56)|~l1_pre_topc(X56))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X57),u1_pre_topc(X57)),X56)|~m1_pre_topc(X57,X56)|~l1_pre_topc(X56))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.64/0.83  fof(c_0_30, plain, ![X58, X59, X60]:((~m1_pre_topc(X59,X58)|m1_pre_topc(X60,X58)|X59!=g1_pre_topc(u1_struct_0(X60),u1_pre_topc(X60))|(~v2_pre_topc(X60)|~l1_pre_topc(X60))|(~v2_pre_topc(X59)|~l1_pre_topc(X59))|~l1_pre_topc(X58))&(~m1_pre_topc(X60,X58)|m1_pre_topc(X59,X58)|X59!=g1_pre_topc(u1_struct_0(X60),u1_pre_topc(X60))|(~v2_pre_topc(X60)|~l1_pre_topc(X60))|(~v2_pre_topc(X59)|~l1_pre_topc(X59))|~l1_pre_topc(X58))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.64/0.83  fof(c_0_31, plain, ![X30]:(~l1_pre_topc(X30)|(~v2_pre_topc(g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))|v2_pre_topc(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).
% 0.64/0.83  cnf(c_0_32, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.64/0.83  cnf(c_0_33, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.64/0.83  fof(c_0_34, plain, ![X66]:(~l1_pre_topc(X66)|m1_pre_topc(X66,X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.64/0.83  fof(c_0_35, plain, ![X17, X18]:(~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|v2_pre_topc(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.64/0.83  fof(c_0_36, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 0.64/0.83  fof(c_0_37, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.64/0.83  cnf(c_0_38, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.64/0.83  cnf(c_0_39, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.64/0.83  cnf(c_0_40, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.64/0.83  cnf(c_0_41, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.64/0.83  cnf(c_0_42, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.64/0.83  fof(c_0_43, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0))&((v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0))&(m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])])).
% 0.64/0.83  fof(c_0_44, plain, ![X67, X68, X69]:((~r1_tarski(u1_struct_0(X68),u1_struct_0(X69))|m1_pre_topc(X68,X69)|~m1_pre_topc(X69,X67)|~m1_pre_topc(X68,X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))&(~m1_pre_topc(X68,X69)|r1_tarski(u1_struct_0(X68),u1_struct_0(X69))|~m1_pre_topc(X69,X67)|~m1_pre_topc(X68,X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.64/0.83  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.64/0.83  fof(c_0_46, plain, ![X31, X32]:((~m1_pre_topc(X31,X32)|m1_pre_topc(X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))|~l1_pre_topc(X32)|~l1_pre_topc(X31))&(~m1_pre_topc(X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))|m1_pre_topc(X31,X32)|~l1_pre_topc(X32)|~l1_pre_topc(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.64/0.83  cnf(c_0_47, plain, (m1_pre_topc(X1,X2)|~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_38, c_0_32])]), c_0_39])).
% 0.64/0.83  cnf(c_0_48, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.64/0.83  cnf(c_0_49, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.64/0.83  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.64/0.83  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.64/0.83  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.64/0.83  cnf(c_0_53, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.64/0.83  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.64/0.83  fof(c_0_55, plain, ![X44, X45]:(((v1_pre_topc(k8_tmap_1(X44,X45))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|~m1_pre_topc(X45,X44)))&(v2_pre_topc(k8_tmap_1(X44,X45))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|~m1_pre_topc(X45,X44))))&(l1_pre_topc(k8_tmap_1(X44,X45))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|~m1_pre_topc(X45,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.64/0.83  cnf(c_0_56, plain, (m1_pre_topc(X1,X2)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.64/0.83  cnf(c_0_57, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_48])).
% 0.64/0.83  cnf(c_0_58, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])])).
% 0.64/0.83  cnf(c_0_59, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_50]), c_0_52])])).
% 0.64/0.83  fof(c_0_60, plain, ![X53, X54, X55]:((u1_struct_0(k8_tmap_1(X53,X54))=u1_struct_0(X53)|(v2_struct_0(X54)|~m1_pre_topc(X54,X53))|(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)))&(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))|(X55!=u1_struct_0(X54)|u1_pre_topc(k8_tmap_1(X53,X54))=k5_tmap_1(X53,X55))|(v2_struct_0(X54)|~m1_pre_topc(X54,X53))|(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.64/0.83  cnf(c_0_61, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.64/0.83  cnf(c_0_62, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.64/0.83  fof(c_0_63, plain, ![X70, X71, X72]:(~v2_pre_topc(X70)|~l1_pre_topc(X70)|(~m1_pre_topc(X71,X70)|(~m1_pre_topc(X72,X71)|m1_pre_topc(X72,X70)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.64/0.83  cnf(c_0_64, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.64/0.83  cnf(c_0_65, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_56, c_0_33])).
% 0.64/0.83  cnf(c_0_66, negated_conjecture, (m1_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.64/0.83  cnf(c_0_67, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_50]), c_0_52])])).
% 0.64/0.83  fof(c_0_68, plain, ![X64, X65]:(~l1_pre_topc(X64)|(~m1_pre_topc(X65,X64)|m1_subset_1(u1_struct_0(X65),k1_zfmisc_1(u1_struct_0(X64))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.64/0.83  cnf(c_0_69, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.64/0.83  cnf(c_0_70, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_50]), c_0_51]), c_0_52])])).
% 0.64/0.83  cnf(c_0_71, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_50]), c_0_51]), c_0_52])])).
% 0.64/0.83  cnf(c_0_72, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.64/0.83  cnf(c_0_73, plain, (v2_struct_0(X1)|l1_pre_topc(k8_tmap_1(X1,X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_41])).
% 0.64/0.83  cnf(c_0_74, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.64/0.83  cnf(c_0_75, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.64/0.83  cnf(c_0_76, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_64, c_0_32])).
% 0.64/0.83  cnf(c_0_77, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_59])])).
% 0.64/0.83  fof(c_0_78, plain, ![X46, X47]:((~r2_hidden(X47,u1_pre_topc(X46))|u1_pre_topc(X46)=k5_tmap_1(X46,X47)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(u1_pre_topc(X46)!=k5_tmap_1(X46,X47)|r2_hidden(X47,u1_pre_topc(X46))|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.64/0.83  cnf(c_0_79, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.64/0.83  cnf(c_0_80, negated_conjecture, (u1_struct_0(k8_tmap_1(esk4_0,esk4_0))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_59])]), c_0_72])).
% 0.64/0.83  cnf(c_0_81, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_71]), c_0_59])]), c_0_72])).
% 0.64/0.83  cnf(c_0_82, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.64/0.83  cnf(c_0_83, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[c_0_74, c_0_75])).
% 0.64/0.83  cnf(c_0_84, plain, (m1_pre_topc(X1,X2)|~m1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X2)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.64/0.83  cnf(c_0_85, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_77]), c_0_71]), c_0_59])])).
% 0.64/0.83  cnf(c_0_86, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.64/0.83  cnf(c_0_87, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_pre_topc(X1,k8_tmap_1(esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.64/0.83  cnf(c_0_88, plain, (k5_tmap_1(X1,u1_struct_0(X2))=u1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]), c_0_79])).
% 0.64/0.83  cnf(c_0_89, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.64/0.83  cnf(c_0_90, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_51]), c_0_52])])).
% 0.64/0.83  cnf(c_0_91, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_83, c_0_41])).
% 0.64/0.83  cnf(c_0_92, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_58]), c_0_67]), c_0_59])])).
% 0.64/0.83  cnf(c_0_93, plain, (v2_pre_topc(X1)|~m1_pre_topc(X1,X2)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_76]), c_0_48])).
% 0.64/0.83  cnf(c_0_94, negated_conjecture, (k5_tmap_1(esk4_0,u1_struct_0(X1))=u1_pre_topc(esk4_0)|~m1_pre_topc(X1,k8_tmap_1(esk4_0,esk4_0))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_71]), c_0_59])]), c_0_72])).
% 0.64/0.83  cnf(c_0_95, negated_conjecture, (k5_tmap_1(esk4_0,u1_struct_0(esk4_0))=u1_pre_topc(k8_tmap_1(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_70]), c_0_71]), c_0_59])]), c_0_72])).
% 0.64/0.83  fof(c_0_96, plain, ![X10]:m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.64/0.83  fof(c_0_97, plain, ![X9]:k2_subset_1(X9)=X9, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.64/0.83  cnf(c_0_98, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~r1_tarski(u1_struct_0(esk4_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.64/0.83  cnf(c_0_99, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_91, c_0_80])).
% 0.64/0.83  cnf(c_0_100, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_92]), c_0_67])])).
% 0.64/0.83  cnf(c_0_101, negated_conjecture, (v2_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_58]), c_0_59])])).
% 0.64/0.83  cnf(c_0_102, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk4_0,esk4_0))=u1_pre_topc(esk4_0)|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),k8_tmap_1(esk4_0,esk4_0))|~r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_80]), c_0_95])).
% 0.64/0.83  fof(c_0_103, plain, ![X19, X20]:((~v3_pre_topc(X20,X19)|r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~r2_hidden(X20,u1_pre_topc(X19))|v3_pre_topc(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.64/0.83  cnf(c_0_104, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.64/0.83  cnf(c_0_105, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.64/0.83  cnf(c_0_106, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.64/0.83  cnf(c_0_107, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_33]), c_0_32])).
% 0.64/0.83  cnf(c_0_108, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(X1)|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)|~m1_pre_topc(X1,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_101])).
% 0.64/0.83  fof(c_0_109, plain, ![X16]:(~l1_pre_topc(X16)|(~v1_pre_topc(X16)|X16=g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.64/0.83  cnf(c_0_110, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.64/0.83  cnf(c_0_111, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk4_0,esk4_0))=u1_pre_topc(esk4_0)|~r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_41]), c_0_81])])).
% 0.64/0.83  cnf(c_0_112, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.64/0.83  cnf(c_0_113, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.64/0.83  cnf(c_0_114, plain, (v2_struct_0(X1)|v1_pre_topc(k8_tmap_1(X1,X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_106, c_0_41])).
% 0.64/0.83  cnf(c_0_115, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_50]), c_0_51]), c_0_52])])).
% 0.64/0.83  cnf(c_0_116, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_92]), c_0_77])])).
% 0.64/0.83  cnf(c_0_117, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.64/0.83  cnf(c_0_118, negated_conjecture, (v1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_50]), c_0_52])])).
% 0.64/0.83  cnf(c_0_119, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk4_0,esk4_0))=u1_pre_topc(esk4_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_59]), c_0_113])])).
% 0.64/0.83  cnf(c_0_120, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_71]), c_0_59])]), c_0_72])).
% 0.64/0.83  fof(c_0_121, plain, ![X38, X39, X40]:((~v1_tsep_1(X39,X38)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|(X40!=u1_struct_0(X39)|v3_pre_topc(X40,X38)))|~m1_pre_topc(X39,X38)|~l1_pre_topc(X38))&((m1_subset_1(esk2_2(X38,X39),k1_zfmisc_1(u1_struct_0(X38)))|v1_tsep_1(X39,X38)|~m1_pre_topc(X39,X38)|~l1_pre_topc(X38))&((esk2_2(X38,X39)=u1_struct_0(X39)|v1_tsep_1(X39,X38)|~m1_pre_topc(X39,X38)|~l1_pre_topc(X38))&(~v3_pre_topc(esk2_2(X38,X39),X38)|v1_tsep_1(X39,X38)|~m1_pre_topc(X39,X38)|~l1_pre_topc(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.64/0.83  cnf(c_0_122, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.64/0.83  cnf(c_0_123, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.64/0.83  cnf(c_0_124, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))),esk3_0)|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_77])])).
% 0.64/0.83  cnf(c_0_125, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_116]), c_0_118]), c_0_67])])).
% 0.64/0.83  cnf(c_0_126, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k8_tmap_1(esk4_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_119]), c_0_80]), c_0_120]), c_0_81])])).
% 0.64/0.83  cnf(c_0_127, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.64/0.83  fof(c_0_128, plain, ![X61, X62, X63]:((v1_tsep_1(X62,X63)|~r1_tarski(u1_struct_0(X62),u1_struct_0(X63))|(v2_struct_0(X63)|~m1_pre_topc(X63,X61))|(~v1_tsep_1(X62,X61)|~m1_pre_topc(X62,X61))|(v2_struct_0(X61)|~v2_pre_topc(X61)|~l1_pre_topc(X61)))&(m1_pre_topc(X62,X63)|~r1_tarski(u1_struct_0(X62),u1_struct_0(X63))|(v2_struct_0(X63)|~m1_pre_topc(X63,X61))|(~v1_tsep_1(X62,X61)|~m1_pre_topc(X62,X61))|(v2_struct_0(X61)|~v2_pre_topc(X61)|~l1_pre_topc(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_tsep_1])])])])])).
% 0.64/0.83  cnf(c_0_129, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_122]), c_0_52])])).
% 0.64/0.83  cnf(c_0_130, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_50]), c_0_51]), c_0_52])]), c_0_123])).
% 0.64/0.83  cnf(c_0_131, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_122]), c_0_52])])).
% 0.64/0.83  cnf(c_0_132, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 0.64/0.83  cnf(c_0_133, negated_conjecture, (m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)|~v3_pre_topc(u1_struct_0(esk4_0),esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_126])).
% 0.64/0.83  cnf(c_0_134, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_127]), c_0_79])).
% 0.64/0.83  cnf(c_0_135, plain, (v1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~v1_tsep_1(X1,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_128])).
% 0.64/0.83  cnf(c_0_136, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_33]), c_0_130])])).
% 0.64/0.83  cnf(c_0_137, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(esk4_0,k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_131, c_0_50])).
% 0.64/0.83  cnf(c_0_138, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_132]), c_0_51]), c_0_52]), c_0_59])])).
% 0.64/0.83  cnf(c_0_139, negated_conjecture, (m1_pre_topc(k8_tmap_1(esk4_0,esk4_0),X1)|~v1_tsep_1(esk4_0,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_70]), c_0_59])])).
% 0.64/0.83  cnf(c_0_140, negated_conjecture, (v1_tsep_1(X1,esk4_0)|v2_struct_0(X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,esk4_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_90]), c_0_72]), c_0_75])).
% 0.64/0.83  cnf(c_0_141, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_67]), c_0_137])).
% 0.64/0.83  fof(c_0_142, plain, ![X27, X28, X29]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.64/0.83  cnf(c_0_143, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~v1_tsep_1(esk4_0,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_70]), c_0_59])])).
% 0.64/0.83  cnf(c_0_144, negated_conjecture, (v1_tsep_1(X1,esk4_0)|~v1_tsep_1(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_50]), c_0_51]), c_0_52])]), c_0_123])).
% 0.64/0.83  cnf(c_0_145, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_141]), c_0_51]), c_0_52]), c_0_59])])).
% 0.64/0.83  cnf(c_0_146, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_142])).
% 0.64/0.83  cnf(c_0_147, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_70])]), c_0_145])).
% 0.64/0.83  cnf(c_0_148, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_56, c_0_41])).
% 0.64/0.83  cnf(c_0_149, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_79]), c_0_32])).
% 0.64/0.83  cnf(c_0_150, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_148]), c_0_67]), c_0_59])])).
% 0.64/0.83  cnf(c_0_151, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_52])])).
% 0.64/0.83  cnf(c_0_152, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_151, c_0_66])).
% 0.64/0.83  cnf(c_0_153, negated_conjecture, (k5_tmap_1(esk3_0,u1_struct_0(esk4_0))=u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_50]), c_0_51]), c_0_52])]), c_0_123]), c_0_72])).
% 0.64/0.83  cnf(c_0_154, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))=u1_pre_topc(esk3_0)|~r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_152]), c_0_153]), c_0_51]), c_0_52])]), c_0_123])).
% 0.64/0.83  cnf(c_0_155, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.64/0.83  cnf(c_0_156, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.64/0.83  cnf(c_0_157, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))=u1_pre_topc(esk3_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_112]), c_0_52]), c_0_152])])).
% 0.64/0.83  cnf(c_0_158, negated_conjecture, (u1_struct_0(k8_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_50]), c_0_51]), c_0_52])]), c_0_72]), c_0_123])).
% 0.64/0.83  cnf(c_0_159, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_50]), c_0_51]), c_0_52])]), c_0_123])).
% 0.64/0.83  cnf(c_0_160, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.64/0.83  cnf(c_0_161, negated_conjecture, (esk2_2(esk3_0,esk4_0)=u1_struct_0(esk4_0)|v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_50]), c_0_52])])).
% 0.64/0.83  cnf(c_0_162, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.64/0.83  cnf(c_0_163, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_50])])).
% 0.64/0.83  cnf(c_0_164, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_157]), c_0_158]), c_0_159]), c_0_130])])).
% 0.64/0.83  cnf(c_0_165, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_50]), c_0_52])])).
% 0.64/0.83  fof(c_0_166, plain, ![X50, X51, X52]:(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X50,X51))))|(X52!=X51|v3_pre_topc(X52,k6_tmap_1(X50,X51)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).
% 0.64/0.83  fof(c_0_167, plain, ![X48, X49]:((u1_struct_0(k6_tmap_1(X48,X49))=u1_struct_0(X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(u1_pre_topc(k6_tmap_1(X48,X49))=k5_tmap_1(X48,X49)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.64/0.83  cnf(c_0_168, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_76]), c_0_48])).
% 0.64/0.83  cnf(c_0_169, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)))=k8_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_158]), c_0_159]), c_0_130])])).
% 0.64/0.83  cnf(c_0_170, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_50]), c_0_51]), c_0_52])]), c_0_123])).
% 0.64/0.83  cnf(c_0_171, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_165])).
% 0.64/0.83  fof(c_0_172, plain, ![X33, X34, X35, X36]:((X35!=k8_tmap_1(X33,X34)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))|(X36!=u1_struct_0(X34)|X35=k6_tmap_1(X33,X36)))|(~v1_pre_topc(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))|~m1_pre_topc(X34,X33)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&((m1_subset_1(esk1_3(X33,X34,X35),k1_zfmisc_1(u1_struct_0(X33)))|X35=k8_tmap_1(X33,X34)|(~v1_pre_topc(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))|~m1_pre_topc(X34,X33)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&((esk1_3(X33,X34,X35)=u1_struct_0(X34)|X35=k8_tmap_1(X33,X34)|(~v1_pre_topc(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))|~m1_pre_topc(X34,X33)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(X35!=k6_tmap_1(X33,esk1_3(X33,X34,X35))|X35=k8_tmap_1(X33,X34)|(~v1_pre_topc(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))|~m1_pre_topc(X34,X33)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.64/0.83  cnf(c_0_173, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(esk3_0,k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_41]), c_0_52])])).
% 0.64/0.83  cnf(c_0_174, plain, (v2_struct_0(X1)|v3_pre_topc(X3,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|X3!=X2), inference(split_conjunct,[status(thm)],[c_0_166])).
% 0.64/0.83  cnf(c_0_175, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_167])).
% 0.64/0.83  cnf(c_0_176, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_158]), c_0_130])])).
% 0.64/0.83  cnf(c_0_177, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_158]), c_0_169]), c_0_170]), c_0_130])])).
% 0.64/0.83  cnf(c_0_178, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_131, c_0_141])).
% 0.64/0.83  cnf(c_0_179, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_134]), c_0_50]), c_0_52])])).
% 0.64/0.83  cnf(c_0_180, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_172])).
% 0.64/0.83  cnf(c_0_181, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_173]), c_0_170]), c_0_130])])).
% 0.64/0.83  cnf(c_0_182, plain, (v2_struct_0(X1)|v3_pre_topc(X2,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_174])).
% 0.64/0.83  cnf(c_0_183, negated_conjecture, (u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(X1)))=u1_struct_0(esk3_0)|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_176]), c_0_51]), c_0_52])]), c_0_123])).
% 0.64/0.83  cnf(c_0_184, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(X1)|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(esk4_0,X1)), inference(spm,[status(thm)],[c_0_98, c_0_177])).
% 0.64/0.83  cnf(c_0_185, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[c_0_178, c_0_179])).
% 0.64/0.83  cnf(c_0_186, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_180])]), c_0_79]), c_0_62]), c_0_106]), c_0_162])).
% 0.64/0.83  fof(c_0_187, plain, ![X24]:(~v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.64/0.83  fof(c_0_188, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.64/0.83  cnf(c_0_189, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_181, c_0_50])).
% 0.64/0.83  cnf(c_0_190, negated_conjecture, (esk2_2(k8_tmap_1(esk3_0,esk4_0),esk4_0)=u1_struct_0(esk4_0)|v1_tsep_1(esk4_0,k8_tmap_1(esk3_0,esk4_0))|v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_137]), c_0_130])])).
% 0.64/0.83  cnf(c_0_191, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),k6_tmap_1(esk3_0,u1_struct_0(X1)))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_183]), c_0_51]), c_0_52])]), c_0_123]), c_0_176])).
% 0.64/0.83  cnf(c_0_192, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_185]), c_0_77]), c_0_66])])).
% 0.64/0.83  cnf(c_0_193, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))=k8_tmap_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_50]), c_0_51]), c_0_52])]), c_0_123])).
% 0.64/0.83  cnf(c_0_194, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_187])).
% 0.64/0.83  cnf(c_0_195, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_188])).
% 0.64/0.83  cnf(c_0_196, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[c_0_189, c_0_179])).
% 0.64/0.83  cnf(c_0_197, negated_conjecture, (m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_75, c_0_50])).
% 0.64/0.83  cnf(c_0_198, negated_conjecture, (v1_tsep_1(esk4_0,k8_tmap_1(esk3_0,esk4_0))|v1_tsep_1(esk4_0,esk3_0)|~v3_pre_topc(u1_struct_0(esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_190]), c_0_130])]), c_0_137])).
% 0.64/0.83  cnf(c_0_199, negated_conjecture, (v3_pre_topc(u1_struct_0(esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_192]), c_0_193]), c_0_185])])).
% 0.64/0.83  fof(c_0_200, plain, ![X25]:(v2_struct_0(X25)|~l1_struct_0(X25)|~v1_xboole_0(u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.64/0.83  cnf(c_0_201, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_194, c_0_195])).
% 0.64/0.83  cnf(c_0_202, negated_conjecture, (v2_struct_0(X1)|~v1_tsep_1(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_196]), c_0_179]), c_0_123]), c_0_197])).
% 0.64/0.83  cnf(c_0_203, negated_conjecture, (v1_tsep_1(esk4_0,k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_198, c_0_199])]), c_0_179])).
% 0.64/0.83  cnf(c_0_204, negated_conjecture, (m1_pre_topc(esk3_0,k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[c_0_173, c_0_179])).
% 0.64/0.83  cnf(c_0_205, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_200])).
% 0.64/0.83  cnf(c_0_206, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~v2_struct_0(k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_158]), c_0_130])])).
% 0.64/0.83  cnf(c_0_207, negated_conjecture, (v2_struct_0(k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_203]), c_0_204]), c_0_170]), c_0_130])])).
% 0.64/0.83  cnf(c_0_208, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_205, c_0_195])).
% 0.64/0.83  cnf(c_0_209, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_206, c_0_207])])).
% 0.64/0.83  cnf(c_0_210, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208, c_0_209]), c_0_52])]), c_0_123]), ['proof']).
% 0.64/0.83  # SZS output end CNFRefutation
% 0.64/0.83  # Proof object total steps             : 211
% 0.64/0.83  # Proof object clause steps            : 154
% 0.64/0.83  # Proof object formula steps           : 57
% 0.64/0.83  # Proof object conjectures             : 95
% 0.64/0.83  # Proof object clause conjectures      : 92
% 0.64/0.83  # Proof object formula conjectures     : 3
% 0.64/0.83  # Proof object initial clauses used    : 43
% 0.64/0.83  # Proof object initial formulas used   : 28
% 0.64/0.83  # Proof object generating inferences   : 96
% 0.64/0.83  # Proof object simplifying inferences  : 237
% 0.64/0.83  # Training examples: 0 positive, 0 negative
% 0.64/0.83  # Parsed axioms                        : 33
% 0.64/0.83  # Removed by relevancy pruning/SinE    : 0
% 0.64/0.83  # Initial clauses                      : 66
% 0.64/0.83  # Removed in clause preprocessing      : 1
% 0.64/0.83  # Initial clauses in saturation        : 65
% 0.64/0.83  # Processed clauses                    : 3472
% 0.64/0.83  # ...of these trivial                  : 101
% 0.64/0.83  # ...subsumed                          : 1770
% 0.64/0.83  # ...remaining for further processing  : 1601
% 0.64/0.83  # Other redundant clauses eliminated   : 9
% 0.64/0.83  # Clauses deleted for lack of memory   : 0
% 0.64/0.83  # Backward-subsumed                    : 261
% 0.64/0.83  # Backward-rewritten                   : 471
% 0.64/0.83  # Generated clauses                    : 21012
% 0.64/0.83  # ...of the previous two non-trivial   : 17456
% 0.64/0.83  # Contextual simplify-reflections      : 251
% 0.64/0.83  # Paramodulations                      : 20945
% 0.64/0.83  # Factorizations                       : 0
% 0.64/0.83  # Equation resolutions                 : 9
% 0.64/0.83  # Propositional unsat checks           : 0
% 0.64/0.83  #    Propositional check models        : 0
% 0.64/0.83  #    Propositional check unsatisfiable : 0
% 0.64/0.83  #    Propositional clauses             : 0
% 0.64/0.83  #    Propositional clauses after purity: 0
% 0.64/0.83  #    Propositional unsat core size     : 0
% 0.64/0.83  #    Propositional preprocessing time  : 0.000
% 0.64/0.83  #    Propositional encoding time       : 0.000
% 0.64/0.83  #    Propositional solver time         : 0.000
% 0.64/0.83  #    Success case prop preproc time    : 0.000
% 0.64/0.83  #    Success case prop encoding time   : 0.000
% 0.64/0.83  #    Success case prop solver time     : 0.000
% 0.64/0.83  # Current number of processed clauses  : 741
% 0.64/0.83  #    Positive orientable unit clauses  : 64
% 0.64/0.83  #    Positive unorientable unit clauses: 0
% 0.64/0.83  #    Negative unit clauses             : 4
% 0.64/0.83  #    Non-unit-clauses                  : 673
% 0.64/0.83  # Current number of unprocessed clauses: 13915
% 0.64/0.83  # ...number of literals in the above   : 62836
% 0.64/0.83  # Current number of archived formulas  : 0
% 0.64/0.83  # Current number of archived clauses   : 853
% 0.64/0.83  # Clause-clause subsumption calls (NU) : 163618
% 0.64/0.83  # Rec. Clause-clause subsumption calls : 60647
% 0.64/0.83  # Non-unit clause-clause subsumptions  : 2203
% 0.64/0.83  # Unit Clause-clause subsumption calls : 4784
% 0.64/0.83  # Rewrite failures with RHS unbound    : 0
% 0.64/0.83  # BW rewrite match attempts            : 182
% 0.64/0.83  # BW rewrite match successes           : 59
% 0.64/0.83  # Condensation attempts                : 0
% 0.64/0.83  # Condensation successes               : 0
% 0.64/0.83  # Termbank termtop insertions          : 532774
% 0.64/0.83  
% 0.64/0.83  # -------------------------------------------------
% 0.64/0.83  # User time                : 0.472 s
% 0.64/0.83  # System time              : 0.020 s
% 0.64/0.83  # Total time               : 0.492 s
% 0.64/0.83  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
