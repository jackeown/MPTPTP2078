%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 231 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   33
%              Number of atoms          :  477 (2025 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(resolution,[],[f102,f63])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_waybel_9(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
            & ! [X2] :
                ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(sK0,X1),sK0)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_waybel_9(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ v4_pre_topc(k6_waybel_0(sK0,X1),sK0)
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) )
             => v4_pre_topc(k6_waybel_0(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) )
           => v4_pre_topc(k6_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_9)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f102,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f100,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f100,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f99,f64])).

fof(f64,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,
    ( ~ l1_orders_2(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f98,f42])).

fof(f42,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f97,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f97,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f95,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f95,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f94,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,
    ( v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f92,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f91,f45])).

fof(f91,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f90,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f87,f38])).

fof(f38,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v8_pre_topc(X0)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_pcomps_1)).

fof(f84,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f82,f70])).

fof(f70,plain,(
    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f69,f45])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0) ) ),
    inference(resolution,[],[f68,f64])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0) ) ),
    inference(resolution,[],[f66,f39])).

fof(f39,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f65,f41])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_9)).

fof(f82,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0)
      | ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f81,f45])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1),sK0)
      | ~ v4_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f79,f46])).

fof(f46,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(sK0,X1),sK0,sK0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X1),X0),sK0)
      | ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f78,f63])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X1),X0),sK0)
      | ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_pre_topc(k4_waybel_1(sK0,X1),sK0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f77,f64])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f75,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
      | ~ v5_pre_topc(k4_waybel_1(X1,X2),X1,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(k4_waybel_1(X1,X2),X1,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_waybel_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(k4_waybel_1(X2,X3),X4,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v1_funct_2(k4_waybel_1(X2,X3),u1_struct_0(X4),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(X1),k4_waybel_1(X2,X3),X0),X4)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v4_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v4_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (10588)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (10590)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (10606)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (10591)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (10604)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (10608)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (10586)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (10594)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (10609)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (10598)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (10594)Refutation not found, incomplete strategy% (10594)------------------------------
% 0.21/0.51  % (10594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10600)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (10592)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (10595)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (10595)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (10602)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (10594)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10594)Memory used [KB]: 10618
% 0.21/0.52  % (10594)Time elapsed: 0.089 s
% 0.21/0.52  % (10594)------------------------------
% 0.21/0.52  % (10594)------------------------------
% 0.21/0.52  % (10592)Refutation not found, incomplete strategy% (10592)------------------------------
% 0.21/0.52  % (10592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10592)Memory used [KB]: 10746
% 0.21/0.52  % (10592)Time elapsed: 0.103 s
% 0.21/0.52  % (10592)------------------------------
% 0.21/0.52  % (10592)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f102,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f48,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    l1_waybel_9(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    (~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f31,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK0,X1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X1] : (~v4_pre_topc(k6_waybel_0(sK0,X1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_9)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f100,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f99,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    l1_orders_2(sK0)),
% 0.21/0.52    inference(resolution,[],[f49,f44])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~l1_orders_2(sK0) | ~l1_pre_topc(sK0) | ~l1_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f98,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    v1_lattice3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~v1_lattice3(sK0) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK0) | ~l1_orders_2(sK0)),
% 0.21/0.52    inference(resolution,[],[f97,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~l1_struct_0(sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f95,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f94,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f93,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f92,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)),
% 0.21/0.52    inference(resolution,[],[f91,f45])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(resolution,[],[f90,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(resolution,[],[f87,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v8_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~v8_pre_topc(sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v8_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f84,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_pcomps_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.52    inference(superposition,[],[f82,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.52    inference(resolution,[],[f69,f45])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f68,f64])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f66,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    v3_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_orders_2(sK0) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f65,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    v5_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),k6_domain_1(u1_struct_0(sK0),X0)) = k6_waybel_0(sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f58,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    v2_lattice3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_9)).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f81,f45])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1),sK0) | ~v4_pre_topc(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.52    inference(resolution,[],[f79,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_pre_topc(k4_waybel_1(sK0,X1),sK0,sK0) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X1),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f78,f63])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X1),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,X1),sK0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f77,f64])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f75,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1)) | ~v5_pre_topc(k4_waybel_1(X1,X2),X1,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(k4_waybel_1(X1,X2),X1,X1) | ~v4_pre_topc(X0,X1) | ~v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0),X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(resolution,[],[f71,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k4_waybel_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(k4_waybel_1(X2,X3),X4,X1) | ~v4_pre_topc(X0,X1) | ~v1_funct_2(k4_waybel_1(X2,X3),u1_struct_0(X4),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(X1),k4_waybel_1(X2,X3),X0),X4) | ~l1_pre_topc(X1) | ~l1_pre_topc(X4) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.52    inference(resolution,[],[f52,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v4_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v4_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (10595)------------------------------
% 0.21/0.52  % (10595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10595)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (10595)Memory used [KB]: 1663
% 0.21/0.52  % (10595)Time elapsed: 0.103 s
% 0.21/0.52  % (10595)------------------------------
% 0.21/0.52  % (10595)------------------------------
% 0.21/0.52  % (10597)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (10585)Success in time 0.163 s
%------------------------------------------------------------------------------
