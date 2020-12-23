%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 625 expanded)
%              Number of leaves         :   16 ( 187 expanded)
%              Depth                    :   26
%              Number of atoms          :  569 (5367 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(subsumption_resolution,[],[f347,f55])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f347,plain,(
    ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f344,f56])).

fof(f56,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f344,plain,(
    ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f339,f156])).

fof(f156,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f52,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f146,plain,
    ( ~ v2_struct_0(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
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

% (30243)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (30247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (30241)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (30244)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% (30247)Refutation not found, incomplete strategy% (30247)------------------------------
% (30247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30247)Termination reason: Refutation not found, incomplete strategy

% (30247)Memory used [KB]: 10618
% (30247)Time elapsed: 0.075 s
% (30247)------------------------------
% (30247)------------------------------
fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f92,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f54,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f339,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f292,f110])).

fof(f110,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f91])).

fof(f91,plain,(
    l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f58])).

fof(f58,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f108,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f48,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f292,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f291,f288])).

fof(f288,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f218,f240])).

fof(f240,plain,(
    m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f233,f211])).

fof(f211,plain,(
    m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f121,f156])).

fof(f121,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f101,f92])).

fof(f101,plain,
    ( m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f233,plain,
    ( m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(superposition,[],[f77,f118])).

fof(f118,plain,(
    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f117,f49])).

fof(f49,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f116,f51])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f116,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v5_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f53,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f115,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f98,f92])).

fof(f98,plain,
    ( k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f55,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f199,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f199,plain,(
    r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f198,f156])).

fof(f198,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f92])).

fof(f197,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f195,f55])).

fof(f195,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f192,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

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

fof(f192,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f191,f49])).

fof(f191,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f190,f92])).

fof(f190,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f189,f55])).

fof(f189,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f188,f156])).

fof(f188,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,
    ( v2_struct_0(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f131,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
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
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f131,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f130,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f92])).

fof(f106,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r3_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f291,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f290,f55])).

fof(f290,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f239,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f239,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) ),
    inference(subsumption_resolution,[],[f238,f91])).

fof(f238,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f237,f185])).

fof(f185,plain,(
    v1_funct_1(k4_waybel_1(sK0,sK1)) ),
    inference(resolution,[],[f119,f156])).

fof(f119,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_waybel_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f99,f92])).

fof(f99,plain,
    ( v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f237,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f236,f203])).

fof(f203,plain,(
    v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f120,f156])).

fof(f120,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f100,f92])).

fof(f100,plain,
    ( v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f236,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f235,f211])).

fof(f235,plain,
    ( ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f234,f57])).

fof(f57,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f234,plain,
    ( v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,
    ( v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)
    | ~ m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f60,f118])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v4_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (30250)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.45  % (30258)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.46  % (30240)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.47  % (30250)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f356,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f347,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    (~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f39,f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK0,X1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ? [X1] : (~v4_pre_topc(k6_waybel_0(sK0,X1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.47    inference(flattening,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,negated_conjecture,(
% 0.19/0.47    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.19/0.47    inference(negated_conjecture,[],[f13])).
% 0.19/0.47  fof(f13,conjecture,(
% 0.19/0.47    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_waybel_9)).
% 0.19/0.47  fof(f347,plain,(
% 0.19/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.47    inference(resolution,[],[f344,f56])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f344,plain,(
% 0.19/0.47    ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f339,f156])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    ~v2_struct_0(sK0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f146,f52])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    v1_lattice3(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f146,plain,(
% 0.19/0.47    ~v2_struct_0(sK0) | ~v1_lattice3(sK0)),
% 0.19/0.47    inference(resolution,[],[f92,f64])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.19/0.47    inference(flattening,[],[f20])).
% 0.19/0.48  % (30243)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.48  % (30247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.48  % (30241)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.48  % (30244)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.48  % (30247)Refutation not found, incomplete strategy% (30247)------------------------------
% 0.19/0.48  % (30247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (30247)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (30247)Memory used [KB]: 10618
% 0.19/0.48  % (30247)Time elapsed: 0.075 s
% 0.19/0.48  % (30247)------------------------------
% 0.19/0.48  % (30247)------------------------------
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.19/0.48  fof(f92,plain,(
% 0.19/0.48    l1_orders_2(sK0)),
% 0.19/0.48    inference(resolution,[],[f54,f59])).
% 0.19/0.48  fof(f59,plain,(
% 0.19/0.48    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    l1_waybel_9(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f40])).
% 0.19/0.48  fof(f339,plain,(
% 0.19/0.48    ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f292,f110])).
% 0.19/0.48  fof(f110,plain,(
% 0.19/0.48    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f109,f47])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    v2_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f40])).
% 0.19/0.48  fof(f109,plain,(
% 0.19/0.48    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f108,f91])).
% 0.19/0.48  fof(f91,plain,(
% 0.19/0.48    l1_pre_topc(sK0)),
% 0.19/0.48    inference(resolution,[],[f54,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f108,plain,(
% 0.19/0.48    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f93,f48])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    v8_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f40])).
% 0.19/0.48  fof(f93,plain,(
% 0.19/0.48    v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v8_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f55,f65])).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,axiom,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).
% 0.19/0.48  fof(f292,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f291,f288])).
% 0.19/0.48  fof(f288,plain,(
% 0.19/0.48    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.48    inference(resolution,[],[f218,f240])).
% 0.19/0.48  fof(f240,plain,(
% 0.19/0.48    m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.48    inference(subsumption_resolution,[],[f233,f211])).
% 0.19/0.48  fof(f211,plain,(
% 0.19/0.48    m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.19/0.48    inference(resolution,[],[f121,f156])).
% 0.19/0.48  fof(f121,plain,(
% 0.19/0.48    v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.19/0.48    inference(subsumption_resolution,[],[f101,f92])).
% 0.19/0.48  fof(f101,plain,(
% 0.19/0.48    m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f55,f72])).
% 0.19/0.48  fof(f72,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.19/0.48  fof(f233,plain,(
% 0.19/0.48    m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.19/0.48    inference(superposition,[],[f77,f118])).
% 0.19/0.48  fof(f118,plain,(
% 0.19/0.48    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.19/0.48    inference(subsumption_resolution,[],[f117,f49])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    v3_orders_2(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f40])).
% 0.19/0.48  fof(f117,plain,(
% 0.19/0.48    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f116,f51])).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    v5_orders_2(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f40])).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f115,f53])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    v2_lattice3(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f40])).
% 0.19/0.48  fof(f115,plain,(
% 0.19/0.48    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f98,f92])).
% 0.19/0.48  fof(f98,plain,(
% 0.19/0.48    k6_waybel_0(sK0,sK1) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(resolution,[],[f55,f68])).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.19/0.48    inference(flattening,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,axiom,(
% 0.19/0.48    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_waybel_0(X0,X1) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).
% 0.19/0.48  fof(f77,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.19/0.48  fof(f218,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.19/0.48    inference(resolution,[],[f199,f76])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f36])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.48  fof(f199,plain,(
% 0.19/0.48    r2_hidden(sK1,k6_waybel_0(sK0,sK1))),
% 0.19/0.48    inference(subsumption_resolution,[],[f198,f156])).
% 0.19/0.48  fof(f198,plain,(
% 0.19/0.48    r2_hidden(sK1,k6_waybel_0(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f197,f92])).
% 0.19/0.48  fof(f197,plain,(
% 0.19/0.48    r2_hidden(sK1,k6_waybel_0(sK0,sK1)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f195,f55])).
% 0.19/0.48  fof(f195,plain,(
% 0.19/0.48    r2_hidden(sK1,k6_waybel_0(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f194])).
% 0.19/0.48  fof(f194,plain,(
% 0.19/0.48    r2_hidden(sK1,k6_waybel_0(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f192,f67])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,k6_waybel_0(X0,X1)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k6_waybel_0(X0,X1)) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r2_hidden(X2,k6_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).
% 0.19/0.48  fof(f192,plain,(
% 0.19/0.48    r1_orders_2(sK0,sK1,sK1)),
% 0.19/0.48    inference(subsumption_resolution,[],[f191,f49])).
% 0.19/0.48  fof(f191,plain,(
% 0.19/0.48    r1_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f190,f92])).
% 0.19/0.48  fof(f190,plain,(
% 0.19/0.48    r1_orders_2(sK0,sK1,sK1) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f189,f55])).
% 0.19/0.48  fof(f189,plain,(
% 0.19/0.48    r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f188,f156])).
% 0.19/0.48  fof(f188,plain,(
% 0.19/0.48    v2_struct_0(sK0) | r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f187])).
% 0.19/0.48  fof(f187,plain,(
% 0.19/0.48    v2_struct_0(sK0) | r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f131,f74])).
% 0.19/0.48  fof(f74,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f46])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.19/0.48  fof(f131,plain,(
% 0.19/0.48    r3_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f130,f49])).
% 0.19/0.48  fof(f130,plain,(
% 0.19/0.48    r3_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f106,f92])).
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    r3_orders_2(sK0,sK1,sK1) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f55,f78])).
% 0.19/0.48  fof(f78,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | r3_orders_2(X1,X0,X0) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.19/0.48    inference(condensation,[],[f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.19/0.48  fof(f291,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f290,f55])).
% 0.19/0.48  fof(f290,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.48    inference(resolution,[],[f239,f69])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.48    inference(flattening,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.19/0.48  fof(f239,plain,(
% 0.19/0.48    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f238,f91])).
% 0.19/0.48  fof(f238,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f237,f185])).
% 0.19/0.48  fof(f185,plain,(
% 0.19/0.48    v1_funct_1(k4_waybel_1(sK0,sK1))),
% 0.19/0.48    inference(resolution,[],[f119,f156])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,sK1))),
% 0.19/0.48    inference(subsumption_resolution,[],[f99,f92])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f55,f70])).
% 0.19/0.48  fof(f70,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f31])).
% 0.19/0.48  fof(f237,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f236,f203])).
% 0.19/0.48  fof(f203,plain,(
% 0.19/0.48    v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.19/0.48    inference(resolution,[],[f120,f156])).
% 0.19/0.48  fof(f120,plain,(
% 0.19/0.48    v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f100,f92])).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f55,f71])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f31])).
% 0.19/0.48  fof(f236,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f235,f211])).
% 0.19/0.48  fof(f235,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f234,f57])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    ~v4_pre_topc(k6_waybel_0(sK0,sK1),sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f40])).
% 0.19/0.48  fof(f234,plain,(
% 0.19/0.48    v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f232])).
% 0.19/0.48  fof(f232,plain,(
% 0.19/0.48    v4_pre_topc(k6_waybel_0(sK0,sK1),sK0) | ~v4_pre_topc(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(k4_waybel_1(sK0,sK1),sK0,sK0) | ~m1_subset_1(k4_waybel_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(superposition,[],[f60,f118])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v4_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v4_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(rectify,[],[f41])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (30250)------------------------------
% 0.19/0.48  % (30250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (30250)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (30250)Memory used [KB]: 1791
% 0.19/0.48  % (30250)Time elapsed: 0.063 s
% 0.19/0.48  % (30250)------------------------------
% 0.19/0.48  % (30250)------------------------------
% 0.19/0.49  % (30238)Success in time 0.137 s
%------------------------------------------------------------------------------
