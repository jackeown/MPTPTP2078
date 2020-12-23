%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  197 (3885 expanded)
%              Number of leaves         :   18 (1442 expanded)
%              Depth                    :   33
%              Number of atoms          : 1574 (61867 expanded)
%              Number of equality atoms :   75 (3863 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(subsumption_resolution,[],[f856,f774])).

fof(f774,plain,(
    m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f773,f738])).

fof(f738,plain,(
    m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f737,f64])).

fof(f64,plain,(
    sK1 != k1_waybel_9(sK0,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( sK1 != k1_waybel_9(sK0,sK2)
    & r3_waybel_9(sK0,sK2,sK1)
    & v11_waybel_0(sK2,sK0)
    & ! [X3] :
        ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_waybel_9(sK0)
    & v1_compts_1(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_waybel_9(X0,X2) != X1
                & r3_waybel_9(X0,X2,X1)
                & v11_waybel_0(X2,X0)
                & ! [X3] :
                    ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(sK0,X2) != X1
              & r3_waybel_9(sK0,X2,X1)
              & v11_waybel_0(X2,sK0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & l1_waybel_0(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_waybel_9(sK0)
      & v1_compts_1(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_waybel_9(sK0,X2) != X1
            & r3_waybel_9(sK0,X2,X1)
            & v11_waybel_0(X2,sK0)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & l1_waybel_0(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_waybel_9(sK0,X2) != sK1
          & r3_waybel_9(sK0,X2,sK1)
          & v11_waybel_0(X2,sK0)
          & ! [X3] :
              ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( k1_waybel_9(sK0,X2) != sK1
        & r3_waybel_9(sK0,X2,sK1)
        & v11_waybel_0(X2,sK0)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( sK1 != k1_waybel_9(sK0,sK2)
      & r3_waybel_9(sK0,sK2,sK1)
      & v11_waybel_0(sK2,sK0)
      & ! [X3] :
          ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r3_waybel_9(X0,X2,X1)
                    & v11_waybel_0(X2,X0)
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
                 => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v11_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).

fof(f737,plain,
    ( sK1 = k1_waybel_9(sK0,sK2)
    | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f723,f706])).

fof(f706,plain,(
    k1_waybel_9(sK0,sK2) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f703,f467])).

fof(f467,plain,(
    k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f466,f180])).

fof(f180,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f55,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f55,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f466,plain,
    ( k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f465,f52])).

fof(f52,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f465,plain,
    ( k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f215,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f215,plain,
    ( v2_struct_0(sK0)
    | k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f207,f180])).

fof(f207,plain,
    ( k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_9)).

fof(f60,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f703,plain,(
    k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(resolution,[],[f667,f424])).

fof(f424,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_yellow_2(sK0,X0) = k2_yellow_0(sK0,k2_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f413,f423])).

fof(f423,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f412,f52])).

fof(f412,plain,
    ( ~ v2_struct_0(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(resolution,[],[f180,f68])).

fof(f413,plain,(
    ! [X0] :
      ( k5_yellow_2(sK0,X0) = k2_yellow_0(sK0,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f180,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_yellow_2)).

fof(f667,plain,(
    v1_relat_1(u1_waybel_0(sK0,sK2)) ),
    inference(resolution,[],[f479,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f479,plain,(
    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f210,f411])).

fof(f411,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f180,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f210,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f60,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f723,plain,
    ( m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(resolution,[],[f687,f282])).

fof(f282,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,X0,sK1)
      | m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
      | sK1 = k2_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f281,f51])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f281,plain,(
    ! [X0] :
      ( sK1 = k2_yellow_0(sK0,X0)
      | m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,X0,sK1)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f268,f180])).

fof(f268,plain,(
    ! [X0] :
      ( sK1 = k2_yellow_0(sK0,X0)
      | m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,X0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

% (30919)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f687,plain,(
    r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) ),
    inference(backward_demodulation,[],[f632,f666])).

fof(f666,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2)) ),
    inference(resolution,[],[f479,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f632,plain,(
    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f631,f395])).

fof(f395,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f394,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f394,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f393,f48])).

fof(f48,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f393,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f392,f49])).

fof(f49,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f392,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f391,f50])).

fof(f50,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f391,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f390,f51])).

fof(f390,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f389,f52])).

fof(f389,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f388,f53])).

fof(f53,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f388,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f387,f54])).

fof(f54,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f387,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f386,f55])).

fof(f386,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f385,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f385,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f384,f58])).

fof(f58,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f384,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f383,f59])).

fof(f59,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f383,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f382,f60])).

fof(f382,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f381,f56])).

fof(f381,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f351,f62])).

fof(f62,plain,(
    v11_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f351,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v11_waybel_0(sK2,sK0)
    | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f63,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
                    & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v11_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).

fof(f63,plain,(
    r3_waybel_9(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f631,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f410,f61])).

fof(f61,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f410,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f409,f47])).

fof(f409,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f408,f48])).

fof(f408,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f407,f49])).

fof(f407,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f406,f50])).

fof(f406,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f405,f51])).

fof(f405,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f404,f52])).

fof(f404,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f403,f53])).

fof(f403,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f402,f54])).

fof(f402,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f401,f55])).

fof(f401,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f400,f57])).

fof(f400,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f399,f58])).

fof(f399,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f398,f59])).

fof(f398,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f397,f60])).

% (30926)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f397,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f396,f56])).

fof(f396,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f352,f62])).

fof(f352,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v11_waybel_0(sK2,sK0)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f63,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f773,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f767,f736])).

fof(f736,plain,(
    r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f735,f64])).

fof(f735,plain,
    ( sK1 = k1_waybel_9(sK0,sK2)
    | r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f722,f706])).

fof(f722,plain,
    ( r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(resolution,[],[f687,f284])).

fof(f284,plain,(
    ! [X1] :
      ( ~ r1_lattice3(sK0,X1,sK1)
      | r1_lattice3(sK0,X1,sK5(sK0,sK1,X1))
      | sK1 = k2_yellow_0(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f283,f51])).

fof(f283,plain,(
    ! [X1] :
      ( sK1 = k2_yellow_0(sK0,X1)
      | r1_lattice3(sK0,X1,sK5(sK0,sK1,X1))
      | ~ r1_lattice3(sK0,X1,sK1)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f269,f180])).

fof(f269,plain,(
    ! [X1] :
      ( sK1 = k2_yellow_0(sK0,X1)
      | r1_lattice3(sK0,X1,sK5(sK0,sK1,X1))
      | ~ r1_lattice3(sK0,X1,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f56,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | r1_lattice3(X0,X2,sK5(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f767,plain,
    ( ~ r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f734,f672])).

% (30932)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f672,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f366,f666])).

fof(f366,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f365,f47])).

fof(f365,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f364,f48])).

fof(f364,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f363,f49])).

fof(f363,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f362,f50])).

fof(f362,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f361,f51])).

fof(f361,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f360,f52])).

fof(f360,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f359,f53])).

fof(f359,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f358,f54])).

fof(f358,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f357,f55])).

fof(f357,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f356,f57])).

fof(f356,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f355,f58])).

fof(f355,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f354,f59])).

fof(f354,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f353,f60])).

fof(f353,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f349,f56])).

fof(f349,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f63,f97])).

fof(f97,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
                    & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r1_orders_2(X0,X5,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).

fof(f734,plain,(
    ~ r1_orders_2(sK0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f733,f64])).

fof(f733,plain,
    ( sK1 = k1_waybel_9(sK0,sK2)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),sK1) ),
    inference(forward_demodulation,[],[f721,f706])).

fof(f721,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),sK1)
    | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(resolution,[],[f687,f286])).

fof(f286,plain,(
    ! [X2] :
      ( ~ r1_lattice3(sK0,X2,sK1)
      | ~ r1_orders_2(sK0,sK5(sK0,sK1,X2),sK1)
      | sK1 = k2_yellow_0(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f285,f51])).

fof(f285,plain,(
    ! [X2] :
      ( sK1 = k2_yellow_0(sK0,X2)
      | ~ r1_orders_2(sK0,sK5(sK0,sK1,X2),sK1)
      | ~ r1_lattice3(sK0,X2,sK1)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f270,f180])).

fof(f270,plain,(
    ! [X2] :
      ( sK1 = k2_yellow_0(sK0,X2)
      | ~ r1_orders_2(sK0,sK5(sK0,sK1,X2),sK1)
      | ~ r1_lattice3(sK0,X2,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f56,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f856,plain,(
    ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f772,f61])).

fof(f772,plain,(
    ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ),
    inference(subsumption_resolution,[],[f771,f738])).

fof(f771,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ),
    inference(subsumption_resolution,[],[f766,f736])).

fof(f766,plain,
    ( ~ r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ),
    inference(resolution,[],[f734,f673])).

fof(f673,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ) ),
    inference(backward_demodulation,[],[f380,f666])).

fof(f380,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ) ),
    inference(subsumption_resolution,[],[f379,f47])).

fof(f379,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f378,f48])).

fof(f378,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f377,f49])).

fof(f377,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f376,f50])).

fof(f376,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f375,f51])).

fof(f375,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f374,f52])).

fof(f374,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f373,f53])).

fof(f373,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f372,f54])).

fof(f372,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f371,f55])).

fof(f371,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f370,f57])).

fof(f370,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f369,f58])).

fof(f369,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f368,f59])).

fof(f368,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f367,f60])).

fof(f367,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f350,f56])).

fof(f350,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f63,f96])).

fof(f96,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:46:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (30920)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (30916)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (30931)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (30924)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (30924)Refutation not found, incomplete strategy% (30924)------------------------------
% 0.21/0.49  % (30924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30924)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30924)Memory used [KB]: 6140
% 0.21/0.49  % (30924)Time elapsed: 0.004 s
% 0.21/0.49  % (30924)------------------------------
% 0.21/0.49  % (30924)------------------------------
% 0.21/0.49  % (30917)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (30923)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (30913)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (30913)Refutation not found, incomplete strategy% (30913)------------------------------
% 0.21/0.50  % (30913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30913)Memory used [KB]: 10618
% 0.21/0.50  % (30913)Time elapsed: 0.089 s
% 0.21/0.50  % (30913)------------------------------
% 0.21/0.50  % (30913)------------------------------
% 0.21/0.50  % (30927)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (30914)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (30912)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (30915)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (30912)Refutation not found, incomplete strategy% (30912)------------------------------
% 0.21/0.51  % (30912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30912)Memory used [KB]: 6140
% 0.21/0.51  % (30912)Time elapsed: 0.098 s
% 0.21/0.51  % (30912)------------------------------
% 0.21/0.51  % (30912)------------------------------
% 0.21/0.51  % (30928)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (30921)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (30930)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (30923)Refutation not found, incomplete strategy% (30923)------------------------------
% 0.21/0.51  % (30923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30923)Memory used [KB]: 10874
% 0.21/0.51  % (30923)Time elapsed: 0.104 s
% 0.21/0.51  % (30923)------------------------------
% 0.21/0.51  % (30923)------------------------------
% 0.21/0.51  % (30916)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f857,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f856,f774])).
% 0.21/0.51  fof(f774,plain,(
% 0.21/0.51    m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f773,f738])).
% 0.21/0.51  fof(f738,plain,(
% 0.21/0.51    m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f737,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    sK1 != k1_waybel_9(sK0,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ((sK1 != k1_waybel_9(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v11_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f38,f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_9(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (k1_waybel_9(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_waybel_9(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X2] : (k1_waybel_9(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v11_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (sK1 != k1_waybel_9(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v11_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_9(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).
% 0.21/0.51  fof(f737,plain,(
% 0.21/0.51    sK1 = k1_waybel_9(sK0,sK2) | m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f723,f706])).
% 0.21/0.51  fof(f706,plain,(
% 0.21/0.51    k1_waybel_9(sK0,sK2) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.51    inference(forward_demodulation,[],[f703,f467])).
% 0.21/0.51  fof(f467,plain,(
% 0.21/0.51    k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f466,f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    l1_orders_2(sK0)),
% 0.21/0.51    inference(resolution,[],[f55,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    l1_waybel_9(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f466,plain,(
% 0.21/0.51    k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f465,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v1_lattice3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0)),
% 0.21/0.51    inference(resolution,[],[f215,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    v2_struct_0(sK0) | k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f207,f180])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    k1_waybel_9(sK0,sK2) = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f60,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_9)).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    l1_waybel_0(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f703,plain,(
% 0.21/0.51    k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.51    inference(resolution,[],[f667,f424])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_yellow_2(sK0,X0) = k2_yellow_0(sK0,k2_relat_1(X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f413,f423])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f412,f52])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.51    inference(resolution,[],[f180,f68])).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    ( ! [X0] : (k5_yellow_2(sK0,X0) = k2_yellow_0(sK0,k2_relat_1(X0)) | ~v1_relat_1(X0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f180,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_yellow_2)).
% 0.21/0.51  fof(f667,plain,(
% 0.21/0.51    v1_relat_1(u1_waybel_0(sK0,sK2))),
% 0.21/0.51    inference(resolution,[],[f479,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f479,plain,(
% 0.21/0.52    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.21/0.52    inference(resolution,[],[f210,f411])).
% 0.21/0.52  fof(f411,plain,(
% 0.21/0.52    l1_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f180,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.21/0.52    inference(resolution,[],[f60,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.52  fof(f723,plain,(
% 0.21/0.52    m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.52    inference(resolution,[],[f687,f282])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f281,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    v5_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ( ! [X0] : (sK1 = k2_yellow_0(sK0,X0) | m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,sK1) | ~v5_orders_2(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f268,f180])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    ( ! [X0] : (sK1 = k2_yellow_0(sK0,X0) | m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f56,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK5(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  % (30919)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.21/0.52    inference(rectify,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f687,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f632,f666])).
% 0.21/0.52  fof(f666,plain,(
% 0.21/0.52    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2))),
% 0.21/0.52    inference(resolution,[],[f479,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f632,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f631,f395])).
% 0.21/0.52  fof(f395,plain,(
% 0.21/0.52    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f394,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f394,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f393,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v8_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f392,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v3_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f392,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f391,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v4_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f391,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f390,f51])).
% 0.21/0.52  fof(f390,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f389,f52])).
% 0.21/0.52  fof(f389,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f388,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v2_lattice3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f388,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f387,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    v1_compts_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f387,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f386,f55])).
% 0.21/0.52  fof(f386,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f385,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~v2_struct_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f384,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    v4_orders_2(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f384,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f383,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    v7_waybel_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f383,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f382,f60])).
% 0.21/0.52  fof(f382,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f381,f56])).
% 0.21/0.52  fof(f381,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f351,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    v11_waybel_0(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v11_waybel_0(sK2,sK0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f63,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    r3_waybel_9(sK0,sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f631,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f410,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f410,plain,(
% 0.21/0.52    ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f409,f47])).
% 0.21/0.52  fof(f409,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f408,f48])).
% 0.21/0.52  fof(f408,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f407,f49])).
% 0.21/0.52  fof(f407,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f406,f50])).
% 0.21/0.52  fof(f406,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f405,f51])).
% 0.21/0.52  fof(f405,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f404,f52])).
% 0.21/0.52  fof(f404,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f403,f53])).
% 0.21/0.52  fof(f403,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f402,f54])).
% 0.21/0.52  fof(f402,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f401,f55])).
% 0.21/0.52  fof(f401,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f400,f57])).
% 0.21/0.52  fof(f400,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f399,f58])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f398,f59])).
% 0.21/0.52  fof(f398,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f397,f60])).
% 0.21/0.52  % (30926)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  fof(f397,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f396,f56])).
% 0.21/0.52  fof(f396,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f352,f62])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v11_waybel_0(sK2,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f63,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f773,plain,(
% 0.21/0.52    ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f767,f736])).
% 0.21/0.52  fof(f736,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f735,f64])).
% 0.21/0.52  fof(f735,plain,(
% 0.21/0.52    sK1 = k1_waybel_9(sK0,sK2) | r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.21/0.52    inference(forward_demodulation,[],[f722,f706])).
% 0.21/0.52  fof(f722,plain,(
% 0.21/0.52    r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.52    inference(resolution,[],[f687,f284])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_lattice3(sK0,X1,sK1) | r1_lattice3(sK0,X1,sK5(sK0,sK1,X1)) | sK1 = k2_yellow_0(sK0,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f283,f51])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    ( ! [X1] : (sK1 = k2_yellow_0(sK0,X1) | r1_lattice3(sK0,X1,sK5(sK0,sK1,X1)) | ~r1_lattice3(sK0,X1,sK1) | ~v5_orders_2(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f269,f180])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    ( ! [X1] : (sK1 = k2_yellow_0(sK0,X1) | r1_lattice3(sK0,X1,sK5(sK0,sK1,X1)) | ~r1_lattice3(sK0,X1,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f56,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | r1_lattice3(X0,X2,sK5(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f767,plain,(
% 0.21/0.52    ~r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f734,f672])).
% 0.21/0.52  % (30932)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  fof(f672,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f366,f666])).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f365,f47])).
% 0.21/0.52  fof(f365,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f364,f48])).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f363,f49])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f362,f50])).
% 0.21/0.52  fof(f362,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f361,f51])).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f360,f52])).
% 0.21/0.52  fof(f360,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f359,f53])).
% 0.21/0.52  fof(f359,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f358,f54])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f357,f55])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f356,f57])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f355,f58])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f354,f59])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f353,f60])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f349,f56])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f63,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 0.21/0.52    inference(rectify,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).
% 0.21/0.52  fof(f734,plain,(
% 0.21/0.52    ~r1_orders_2(sK0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f733,f64])).
% 0.21/0.52  fof(f733,plain,(
% 0.21/0.52    sK1 = k1_waybel_9(sK0,sK2) | ~r1_orders_2(sK0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),sK1)),
% 0.21/0.52    inference(forward_demodulation,[],[f721,f706])).
% 0.21/0.52  fof(f721,plain,(
% 0.21/0.52    ~r1_orders_2(sK0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),sK1) | sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.52    inference(resolution,[],[f687,f286])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_lattice3(sK0,X2,sK1) | ~r1_orders_2(sK0,sK5(sK0,sK1,X2),sK1) | sK1 = k2_yellow_0(sK0,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f285,f51])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    ( ! [X2] : (sK1 = k2_yellow_0(sK0,X2) | ~r1_orders_2(sK0,sK5(sK0,sK1,X2),sK1) | ~r1_lattice3(sK0,X2,sK1) | ~v5_orders_2(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f270,f180])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    ( ! [X2] : (sK1 = k2_yellow_0(sK0,X2) | ~r1_orders_2(sK0,sK5(sK0,sK1,X2),sK1) | ~r1_lattice3(sK0,X2,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f56,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,sK5(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f856,plain,(
% 0.21/0.52    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f772,f61])).
% 0.21/0.52  fof(f772,plain,(
% 0.21/0.52    ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f771,f738])).
% 0.21/0.52  fof(f771,plain,(
% 0.21/0.52    ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f766,f736])).
% 0.21/0.52  fof(f766,plain,(
% 0.21/0.52    ~r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)),
% 0.21/0.52    inference(resolution,[],[f734,f673])).
% 0.21/0.52  fof(f673,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)) )),
% 0.21/0.52    inference(backward_demodulation,[],[f380,f666])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f379,f47])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f378,f48])).
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f377,f49])).
% 0.21/0.52  fof(f377,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f376,f50])).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f375,f51])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f374,f52])).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f373,f53])).
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f372,f54])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f371,f55])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f370,f57])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f369,f58])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f368,f59])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f367,f60])).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f350,f56])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    ( ! [X1] : (r1_orders_2(sK0,X1,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f63,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (30922)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (30916)------------------------------
% 0.21/0.52  % (30916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30916)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (30916)Memory used [KB]: 2046
% 0.21/0.52  % (30916)Time elapsed: 0.106 s
% 0.21/0.52  % (30916)------------------------------
% 0.21/0.52  % (30916)------------------------------
% 0.21/0.52  % (30932)Refutation not found, incomplete strategy% (30932)------------------------------
% 0.21/0.52  % (30932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30932)Memory used [KB]: 10618
% 0.21/0.52  % (30932)Time elapsed: 0.116 s
% 0.21/0.52  % (30932)------------------------------
% 0.21/0.52  % (30932)------------------------------
% 0.21/0.52  % (30909)Success in time 0.161 s
%------------------------------------------------------------------------------
