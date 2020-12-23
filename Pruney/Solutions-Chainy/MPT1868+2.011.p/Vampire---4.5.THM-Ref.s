%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 350 expanded)
%              Number of leaves         :   13 ( 112 expanded)
%              Depth                    :   20
%              Number of atoms          :  355 (1647 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f166,f175,f205])).

fof(f205,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f203,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f203,plain,
    ( v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f202,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f199,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f199,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f193,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f193,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f192,f28])).

fof(f192,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f191,f30])).

fof(f191,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f190,f31])).

fof(f190,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f189,f83])).

fof(f83,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_1
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f189,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f186,f67])).

fof(f67,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f66,f28])).

fof(f66,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f65,f30])).

fof(f65,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f42,f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f186,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f182,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(k1_tex_2(X0,X1)))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f43,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f182,plain,
    ( ~ sQ2_eqProxy(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl3_3 ),
    inference(resolution,[],[f180,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f46])).

fof(f180,plain,
    ( ~ sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f178,f62])).

fof(f62,plain,(
    ! [X0] : sQ2_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f46])).

fof(f178,plain,
    ( ~ sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ sQ2_eqProxy(sK0,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f177,f32])).

fof(f32,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X1,X0)
        | ~ sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),X1)
        | ~ sQ2_eqProxy(sK0,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X2)
      | ~ sQ2_eqProxy(X2,X3)
      | ~ sQ2_eqProxy(X0,X1)
      | v2_tex_2(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f46])).

fof(f91,plain,
    ( v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_3
  <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f175,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f173,f28])).

fof(f173,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f172,f30])).

fof(f172,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f169,f31])).

fof(f169,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f166,plain,
    ( spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f165])).

% (22236)Refutation not found, incomplete strategy% (22236)------------------------------
% (22236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22236)Termination reason: Refutation not found, incomplete strategy

% (22236)Memory used [KB]: 10490
% (22236)Time elapsed: 0.060 s
% (22236)------------------------------
% (22236)------------------------------
fof(f165,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f28,f30,f83,f67,f92,f70,f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f88,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_2
  <=> v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f69,f30])).

fof(f69,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f67,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f92,plain,
    ( ~ v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f161,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f29,f30,f30,f28,f67,f87,f31,f124])).

fof(f124,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | v1_tdlat_3(k1_tex_2(X3,X4))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(k1_tex_2(X3,X4),X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(k1_tex_2(X0,X1))
      | v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

fof(f87,plain,
    ( ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22245)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.46  % (22248)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (22248)Refutation not found, incomplete strategy% (22248)------------------------------
% 0.20/0.46  % (22248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22240)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (22248)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (22248)Memory used [KB]: 1663
% 0.20/0.46  % (22248)Time elapsed: 0.052 s
% 0.20/0.46  % (22248)------------------------------
% 0.20/0.46  % (22248)------------------------------
% 0.20/0.47  % (22245)Refutation not found, incomplete strategy% (22245)------------------------------
% 0.20/0.47  % (22245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22245)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (22245)Memory used [KB]: 6396
% 0.20/0.47  % (22245)Time elapsed: 0.065 s
% 0.20/0.47  % (22245)------------------------------
% 0.20/0.47  % (22245)------------------------------
% 0.20/0.47  % (22236)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (22251)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (22240)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f161,f166,f175,f205])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    spl3_1 | ~spl3_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f204])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    $false | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f203,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f24,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f202,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f199,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(resolution,[],[f193,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f192,f28])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f191,f30])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f190,f31])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f189,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl3_1 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f186,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f66,f28])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f65,f30])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f42,f31])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f182,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ2_eqProxy(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(k1_tex_2(X0,X1))) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f43,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ~sQ2_eqProxy(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f180,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f46])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f178,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0] : (sQ2_eqProxy(X0,X0)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f46])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),k6_domain_1(u1_struct_0(sK0),sK1)) | ~sQ2_eqProxy(sK0,sK0) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f177,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~sQ2_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),X1) | ~sQ2_eqProxy(sK0,X0)) ) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f91,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X2) | ~sQ2_eqProxy(X2,X3) | ~sQ2_eqProxy(X0,X1) | v2_tex_2(X1,X3)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f46])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl3_3 <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    $false | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f173,f28])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    v2_struct_0(sK0) | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f172,f30])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f169,f31])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f84,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    spl3_1 | ~spl3_2 | spl3_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.47  % (22236)Refutation not found, incomplete strategy% (22236)------------------------------
% 0.20/0.47  % (22236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22236)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (22236)Memory used [KB]: 10490
% 0.20/0.47  % (22236)Time elapsed: 0.060 s
% 0.20/0.47  % (22236)------------------------------
% 0.20/0.47  % (22236)------------------------------
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    $false | (spl3_1 | ~spl3_2 | spl3_3)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f30,f83,f67,f92,f70,f88,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl3_2 <=> v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f69,f30])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(resolution,[],[f67,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ~v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f90])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    $false | spl3_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f29,f30,f30,f28,f67,f87,f31,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X4,X5,X3] : (~l1_pre_topc(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | v1_tdlat_3(k1_tex_2(X3,X4)) | v2_struct_0(X3) | ~m1_pre_topc(k1_tex_2(X3,X4),X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 0.20/0.48    inference(resolution,[],[f34,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v2_pre_topc(k1_tex_2(X0,X1)) | v1_tdlat_3(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => v1_tdlat_3(k1_tex_2(X0,X1)))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f86])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (22240)------------------------------
% 0.20/0.48  % (22240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22240)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (22240)Memory used [KB]: 6140
% 0.20/0.48  % (22240)Time elapsed: 0.058 s
% 0.20/0.48  % (22240)------------------------------
% 0.20/0.48  % (22240)------------------------------
% 0.20/0.48  % (22234)Success in time 0.125 s
%------------------------------------------------------------------------------
