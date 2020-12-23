%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 417 expanded)
%              Number of leaves         :   18 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          :  420 (1914 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f124,f128,f136,f140,f149,f214])).

fof(f214,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f212,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f212,plain,
    ( v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f211,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f211,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f208,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f208,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f199,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f199,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f198,f32])).

fof(f198,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f197,f34])).

fof(f197,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f196,f35])).

fof(f196,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f195,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_1
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f195,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f192,f77])).

fof(f77,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f76,f32])).

fof(f76,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f75,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f192,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f186,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(k1_tex_2(X0,X1)))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f53,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(f186,plain,
    ( ~ sQ2_eqProxy(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl3_3 ),
    inference(resolution,[],[f178,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f56])).

fof(f178,plain,
    ( ~ sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f176,f72])).

fof(f72,plain,(
    ! [X0] : sQ2_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f56])).

fof(f176,plain,
    ( ~ sQ2_eqProxy(sK0,sK0)
    | ~ sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f157,f98])).

fof(f98,plain,
    ( v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_3
  <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ sQ2_eqProxy(X0,sK0)
      | ~ sQ2_eqProxy(X1,k6_domain_1(u1_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_tex_2(X1,X3)
      | ~ sQ2_eqProxy(X2,X3)
      | ~ v2_tex_2(X0,X2)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f56])).

fof(f149,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f147,f32])).

fof(f147,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f146,f34])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f143,f35])).

fof(f143,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f140,plain,
    ( spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f32,f34,f90,f77,f99,f79,f95,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f95,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_2
  <=> v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f77,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f99,plain,
    ( ~ v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f136,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f134,f32])).

fof(f134,plain,
    ( v2_struct_0(sK0)
    | spl3_6 ),
    inference(subsumption_resolution,[],[f133,f34])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_6 ),
    inference(subsumption_resolution,[],[f130,f35])).

fof(f130,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_6 ),
    inference(resolution,[],[f119,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f119,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_6
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f33,f34,f77,f115,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f115,plain,
    ( ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_5
  <=> v2_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f124,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f34,f77,f111,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f111,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_4
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f120,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f103,f93,f89,f117,f113,f109])).

fof(f103,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f101,f90])).

fof(f101,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_2 ),
    inference(resolution,[],[f94,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tex_1)).

fof(f94,plain,
    ( ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (13025)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (13025)Refutation not found, incomplete strategy% (13025)------------------------------
% 0.20/0.48  % (13025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13025)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (13025)Memory used [KB]: 10490
% 0.20/0.48  % (13025)Time elapsed: 0.059 s
% 0.20/0.48  % (13025)------------------------------
% 0.20/0.48  % (13025)------------------------------
% 0.20/0.48  % (13037)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (13037)Refutation not found, incomplete strategy% (13037)------------------------------
% 0.20/0.48  % (13037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13037)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (13037)Memory used [KB]: 1663
% 0.20/0.48  % (13037)Time elapsed: 0.071 s
% 0.20/0.48  % (13037)------------------------------
% 0.20/0.48  % (13037)------------------------------
% 0.20/0.48  % (13029)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (13026)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (13036)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (13036)Refutation not found, incomplete strategy% (13036)------------------------------
% 0.20/0.49  % (13036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13036)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13036)Memory used [KB]: 6140
% 0.20/0.49  % (13036)Time elapsed: 0.077 s
% 0.20/0.49  % (13036)------------------------------
% 0.20/0.49  % (13036)------------------------------
% 0.20/0.50  % (13030)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (13029)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f120,f124,f128,f136,f140,f149,f214])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    spl3_1 | ~spl3_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f213])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    $false | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f212,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f28,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f211,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f208,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(resolution,[],[f199,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f198,f32])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f197,f34])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f196,f35])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f195,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    spl3_1 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f192,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f76,f32])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f34])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f52,f35])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f186,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sQ2_eqProxy(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(k1_tex_2(X0,X1))) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_proxy_replacement,[],[f53,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    ~sQ2_eqProxy(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f178,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.20/0.50    inference(equality_proxy_axiom,[],[f56])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ~sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f176,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0] : (sQ2_eqProxy(X0,X0)) )),
% 0.20/0.50    inference(equality_proxy_axiom,[],[f56])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ~sQ2_eqProxy(sK0,sK0) | ~sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f157,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl3_3 <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~sQ2_eqProxy(X0,sK0) | ~sQ2_eqProxy(X1,k6_domain_1(u1_struct_0(sK0),sK1))) )),
% 0.20/0.50    inference(resolution,[],[f71,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (v2_tex_2(X1,X3) | ~sQ2_eqProxy(X2,X3) | ~v2_tex_2(X0,X2) | ~sQ2_eqProxy(X0,X1)) )),
% 0.20/0.50    inference(equality_proxy_axiom,[],[f56])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ~spl3_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    $false | ~spl3_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f147,f32])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~spl3_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f146,f34])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f143,f35])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f91,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f89])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl3_1 | ~spl3_2 | spl3_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    $false | (spl3_1 | ~spl3_2 | spl3_3)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f32,f34,f90,f77,f99,f79,f95,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl3_2 <=> v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f34])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f77,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ~v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    $false | spl3_6),
% 0.20/0.50    inference(subsumption_resolution,[],[f134,f32])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    v2_struct_0(sK0) | spl3_6),
% 0.20/0.50    inference(subsumption_resolution,[],[f133,f34])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_6),
% 0.20/0.50    inference(subsumption_resolution,[],[f130,f35])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_6),
% 0.20/0.50    inference(resolution,[],[f119,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~v7_struct_0(k1_tex_2(sK0,sK1)) | spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl3_6 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f125])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    $false | spl3_5),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f33,f34,f77,f115,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ~v2_pre_topc(k1_tex_2(sK0,sK1)) | spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl3_5 <=> v2_pre_topc(k1_tex_2(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    $false | spl3_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f34,f77,f111,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl3_4 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_1 | spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f103,f93,f89,f117,f113,f109])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(k1_tex_2(sK0,sK1)) | (spl3_1 | spl3_2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f101,f90])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl3_2),
% 0.20/0.50    inference(resolution,[],[f94,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (v1_tdlat_3(X0) | ~v7_struct_0(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : ((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | (v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ((~v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tex_1)).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f93])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (13029)------------------------------
% 0.20/0.51  % (13029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13029)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (13029)Memory used [KB]: 6140
% 0.20/0.51  % (13029)Time elapsed: 0.071 s
% 0.20/0.51  % (13029)------------------------------
% 0.20/0.51  % (13029)------------------------------
% 0.20/0.51  % (13023)Success in time 0.15 s
%------------------------------------------------------------------------------
