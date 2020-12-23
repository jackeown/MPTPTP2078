%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 (1046 expanded)
%              Number of leaves         :   15 ( 337 expanded)
%              Depth                    :   20
%              Number of atoms          :  497 (10044 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f183,f128,f129,f191])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f176,f170])).

fof(f170,plain,(
    v4_pre_topc(k1_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f130,f157])).

fof(f157,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f151,f108])).

fof(f108,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f54,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

% (3297)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f151,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f115,f114,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f114,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f48,f49,f50,f51,f52,f91,f70])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ? [X1] :
          ( v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ? [X1] :
          ( v2_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ? [X1] :
          ( v12_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ? [X1] :
          ( v13_waybel_0(X1,X0)
          & v12_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc11_waybel_0)).

fof(f91,plain,(
    l1_orders_2(sK0) ),
    inference(unit_resulting_resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f53,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f49,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,(
    ~ v1_xboole_0(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f49,f50,f51,f52,f91,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f130,plain,(
    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f46,f90,f54,f116,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v8_pre_topc(X0)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).

fof(f116,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f52,f91,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f90,plain,(
    l1_pre_topc(sK0) ),
    inference(unit_resulting_resolution,[],[f53,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f176,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k1_tarski(sK1),sK0)
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f171,f157])).

fof(f171,plain,
    ( ~ v4_pre_topc(k1_tarski(sK1),sK0)
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f150,f157])).

fof(f150,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f149,f90])).

fof(f149,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f148,f127])).

fof(f127,plain,(
    v1_funct_1(k4_waybel_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f91,f54,f116,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(f148,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f147,f124])).

fof(f124,plain,(
    v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f54,f55])).

fof(f55,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f147,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f56,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f146,plain,
    ( v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f58,f139])).

fof(f139,plain,(
    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f112,f91])).

fof(f112,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f110,f50])).

fof(f110,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f106,f52])).

fof(f106,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v4_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f2])).

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

fof(f129,plain,(
    m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f91,f54,f116,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,(
    v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f54,f116,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f183,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f182,f151])).

fof(f182,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f175,f54])).

fof(f175,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f66,f157])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:05:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (3292)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (3300)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (3296)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.53  % (3294)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (3308)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.53  % (3294)Refutation not found, incomplete strategy% (3294)------------------------------
% 0.22/0.53  % (3294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3294)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3294)Memory used [KB]: 10618
% 0.22/0.53  % (3294)Time elapsed: 0.106 s
% 0.22/0.53  % (3294)------------------------------
% 0.22/0.53  % (3294)------------------------------
% 0.22/0.53  % (3308)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (3295)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f183,f128,f129,f191])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.53    inference(subsumption_resolution,[],[f176,f170])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    v4_pre_topc(k1_tarski(sK1),sK0)),
% 0.22/0.53    inference(backward_demodulation,[],[f130,f157])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f151,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.22/0.53    inference(resolution,[],[f54,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    (~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f38,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK0,X1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ? [X1] : (~v4_pre_topc(k6_waybel_0(sK0,X1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  % (3297)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_waybel_9)).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f115,f114,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f48,f49,f50,f51,f52,f91,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0] : ((~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ? [X1] : (v1_waybel_0(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ? [X1] : (v2_waybel_0(X1,X0) & v1_waybel_0(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ? [X1] : (v12_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_waybel_0(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ? [X1] : (v13_waybel_0(X1,X0) & v12_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_waybel_0(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc11_waybel_0)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    l1_orders_2(sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f53,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    l1_waybel_9(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    v2_lattice3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    v1_lattice3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    v5_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    v4_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v3_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ~v1_xboole_0(sK3(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f48,f49,f50,f51,f52,f91,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f46,f90,f54,f116,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f52,f91,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f53,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    v8_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k1_tarski(sK1),sK0) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.53    inference(forward_demodulation,[],[f171,f157])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ~v4_pre_topc(k1_tarski(sK1),sK0) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.53    inference(backward_demodulation,[],[f150,f157])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f149,f90])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f148,f127])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    v1_funct_1(k4_waybel_1(sK0,sK1))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f91,f54,f116,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f147,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f54,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f146,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(superposition,[],[f58,f139])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.22/0.53    inference(subsumption_resolution,[],[f112,f91])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_orders_2(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f111,f48])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f110,f50])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f106,f52])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.22/0.53    inference(resolution,[],[f54,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v4_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v4_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(rectify,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f91,f54,f116,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f91,f54,f116,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f182,f151])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f175,f54])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.54    inference(superposition,[],[f66,f157])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (3308)------------------------------
% 0.22/0.54  % (3308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3308)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (3308)Memory used [KB]: 1791
% 0.22/0.54  % (3308)Time elapsed: 0.114 s
% 0.22/0.54  % (3308)------------------------------
% 0.22/0.54  % (3308)------------------------------
% 0.22/0.54  % (3290)Success in time 0.164 s
%------------------------------------------------------------------------------
