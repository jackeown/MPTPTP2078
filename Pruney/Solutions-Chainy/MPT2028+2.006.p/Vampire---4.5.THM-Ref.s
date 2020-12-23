%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 504 expanded)
%              Number of leaves         :   15 (  89 expanded)
%              Depth                    :   23
%              Number of atoms          :  491 (3440 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(global_subsumption,[],[f86,f117,f121,f141])).

fof(f141,plain,(
    ~ sP4(k6_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f140,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP4(X1) ) ),
    inference(general_splitting,[],[f69,f72_D])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f72_D])).

fof(f72_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f140,plain,(
    r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f139,f116])).

fof(f116,plain,(
    ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f74,f76])).

fof(f76,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f49,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) )
             => v4_pre_topc(k6_waybel_0(X0,X1),X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_waybel_9)).

fof(f74,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f47,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f47,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f139,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f136,f76])).

fof(f136,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f127,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k6_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f127,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f126,f116])).

fof(f126,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f124,f76])).

fof(f124,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f45])).

fof(f45,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f123,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f108,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f108,plain,(
    r3_orders_2(sK0,sK1,sK1) ),
    inference(global_subsumption,[],[f74,f76,f107])).

fof(f107,plain,
    ( v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f106,f84])).

fof(f84,plain,(
    sP3(sK0) ),
    inference(resolution,[],[f41,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f70_D])).

fof(f70_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP3(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f106,plain,
    ( v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ sP3(sK0) ),
    inference(subsumption_resolution,[],[f105,f76])).

fof(f105,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ sP3(sK0) ),
    inference(subsumption_resolution,[],[f85,f45])).

fof(f85,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ sP3(sK0) ),
    inference(resolution,[],[f41,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X1)
      | ~ sP3(X0) ) ),
    inference(general_splitting,[],[f67,f70_D])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f121,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f42,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f120,plain,
    ( v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f119,f104])).

fof(f104,plain,(
    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f103,f45])).

fof(f103,plain,
    ( ~ v3_orders_2(sK0)
    | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f102,f76])).

fof(f102,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f101,f48])).

fof(f48,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).

fof(f119,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)),sK0) ),
    inference(resolution,[],[f115,f90])).

fof(f90,plain,(
    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f74,f76,f89])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f44,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,
    ( v2_struct_0(sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f87,f75])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f77,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v8_pre_topc(sK0)
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v8_pre_topc(X0)
      | v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v8_pre_topc(X0)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).

fof(f115,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f114,f100])).

fof(f100,plain,(
    m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(global_subsumption,[],[f74,f76,f99])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f82,f76])).

fof(f82,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f41,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f113,f98])).

fof(f98,plain,(
    v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f74,f76,f97])).

fof(f97,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f81,f76])).

fof(f81,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f41,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f112,f96])).

fof(f96,plain,(
    v1_funct_1(k4_waybel_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f74,f76,f95])).

fof(f95,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_waybel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f80,f76])).

fof(f80,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_waybel_1(sK0,sK1)) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_waybel_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k4_waybel_1(sK0,sK1))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f111,f75])).

fof(f111,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f109,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f2])).

% (15385)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f109,plain,(
    v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) ),
    inference(resolution,[],[f40,f41])).

fof(f40,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | sP4(k6_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f92,f72])).

fof(f92,plain,(
    m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f74,f76,f91])).

fof(f91,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f78,f76])).

fof(f78,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).

fof(f86,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f41,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (15378)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.48  % (15370)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.48  % (15378)Refutation not found, incomplete strategy% (15378)------------------------------
% 0.20/0.48  % (15378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15370)Refutation not found, incomplete strategy% (15370)------------------------------
% 0.20/0.49  % (15370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15378)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15378)Memory used [KB]: 1663
% 0.20/0.49  % (15378)Time elapsed: 0.071 s
% 0.20/0.49  % (15378)------------------------------
% 0.20/0.49  % (15378)------------------------------
% 0.20/0.49  % (15370)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15370)Memory used [KB]: 10618
% 0.20/0.49  % (15370)Time elapsed: 0.072 s
% 0.20/0.49  % (15370)------------------------------
% 0.20/0.49  % (15370)------------------------------
% 0.20/0.49  % (15373)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (15372)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (15372)Refutation not found, incomplete strategy% (15372)------------------------------
% 0.20/0.49  % (15372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15372)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15372)Memory used [KB]: 10618
% 0.20/0.49  % (15372)Time elapsed: 0.082 s
% 0.20/0.49  % (15372)------------------------------
% 0.20/0.49  % (15372)------------------------------
% 0.20/0.49  % (15377)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (15362)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (15365)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (15366)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (15368)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (15369)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (15364)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (15383)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (15382)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (15384)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (15363)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (15364)Refutation not found, incomplete strategy% (15364)------------------------------
% 0.20/0.51  % (15364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15364)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15364)Memory used [KB]: 10618
% 0.20/0.51  % (15364)Time elapsed: 0.094 s
% 0.20/0.51  % (15364)------------------------------
% 0.20/0.51  % (15364)------------------------------
% 0.20/0.51  % (15382)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(global_subsumption,[],[f86,f117,f121,f141])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ~sP4(k6_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(resolution,[],[f140,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP4(X1)) )),
% 0.20/0.51    inference(general_splitting,[],[f69,f72_D])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP4(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f72_D])).
% 0.20/0.51  fof(f72_D,plain,(
% 0.20/0.51    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP4(X1)) )),
% 0.20/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    r2_hidden(sK1,k6_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f139,f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f74,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    l1_orders_2(sK0)),
% 0.20/0.51    inference(resolution,[],[f49,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    l1_waybel_9(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_waybel_9)).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | ~v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f47,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v1_lattice3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    v2_struct_0(sK0) | r2_hidden(sK1,k6_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f138,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k6_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f136,f76])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k6_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,k6_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(resolution,[],[f127,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,k6_waybel_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    r1_orders_2(sK0,sK1,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f126,f116])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f125,f41])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f124,f76])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f123,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    v3_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f108,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    r3_orders_2(sK0,sK1,sK1)),
% 0.20/0.51    inference(global_subsumption,[],[f74,f76,f107])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f106,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    sP3(sK0)),
% 0.20/0.51    inference(resolution,[],[f41,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f70_D])).
% 0.20/0.51  fof(f70_D,plain,(
% 0.20/0.51    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,u1_struct_0(X0)) ) <=> ~sP3(X0)) )),
% 0.20/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK1) | ~sP3(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f105,f76])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK1) | ~sP3(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f85,f45])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r3_orders_2(sK0,sK1,sK1) | ~sP3(sK0)),
% 0.20/0.51    inference(resolution,[],[f41,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r3_orders_2(X0,X1,X1) | ~sP3(X0)) )),
% 0.20/0.51    inference(general_splitting,[],[f67,f70_D])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f120,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f119,f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f103,f45])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ~v3_orders_2(sK0) | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f102,f76])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f101,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    v2_lattice3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f83,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    v5_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(resolution,[],[f41,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)),sK0)),
% 0.20/0.51    inference(resolution,[],[f115,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.51    inference(global_subsumption,[],[f74,f76,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    v2_struct_0(sK0) | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f88,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    v8_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~v8_pre_topc(sK0) | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f87,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f49,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v8_pre_topc(sK0) | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f77,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v8_pre_topc(sK0) | v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.51    inference(resolution,[],[f41,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v8_pre_topc(X0) | v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f114,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.20/0.51    inference(global_subsumption,[],[f74,f76,f99])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.20/0.51    inference(subsumption_resolution,[],[f82,f76])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.20/0.51    inference(resolution,[],[f41,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.51    inference(global_subsumption,[],[f74,f76,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f81,f76])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f41,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f112,f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    v1_funct_1(k4_waybel_1(sK0,sK1))),
% 0.20/0.51    inference(global_subsumption,[],[f74,f76,f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f80,f76])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,sK1))),
% 0.20/0.51    inference(resolution,[],[f41,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | v1_funct_1(k4_waybel_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f75])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f109,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X1) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  % (15385)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)),
% 0.20/0.51    inference(resolution,[],[f40,f41])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | sP4(k6_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(resolution,[],[f92,f72])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(global_subsumption,[],[f74,f76,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    v2_struct_0(sK0) | m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f78,f76])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(resolution,[],[f41,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(resolution,[],[f41,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (15382)------------------------------
% 0.20/0.51  % (15382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15382)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (15382)Memory used [KB]: 6140
% 0.20/0.51  % (15382)Time elapsed: 0.105 s
% 0.20/0.51  % (15382)------------------------------
% 0.20/0.51  % (15382)------------------------------
% 0.20/0.51  % (15357)Success in time 0.152 s
%------------------------------------------------------------------------------
