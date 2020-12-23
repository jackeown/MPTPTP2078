%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 620 expanded)
%              Number of leaves         :   30 ( 179 expanded)
%              Depth                    :   24
%              Number of atoms          :  737 (3103 expanded)
%              Number of equality atoms :   29 (  70 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f896,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f152,f176,f242,f257,f275,f303,f427,f469,f475,f478,f883,f895])).

fof(f895,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f894])).

fof(f894,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f884,f119])).

fof(f119,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f884,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f61,f115])).

fof(f115,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f61,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f883,plain,
    ( spl5_2
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | spl5_2
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f536,f260,f867,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f867,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | spl5_2
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(subsumption_resolution,[],[f865,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f865,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_2
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(resolution,[],[f861,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f861,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(subsumption_resolution,[],[f858,f118])).

fof(f118,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f858,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(resolution,[],[f854,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f79,f87])).

fof(f87,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f854,plain,
    ( ~ sQ4_eqProxy(u1_struct_0(sK0),k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(resolution,[],[f844,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f87])).

fof(f844,plain,
    ( ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(resolution,[],[f779,f59])).

fof(f779,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) )
    | ~ spl5_5
    | spl5_7
    | spl5_8 ),
    inference(subsumption_resolution,[],[f778,f273])).

fof(f273,plain,
    ( ~ v7_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl5_8
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f778,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | v7_struct_0(sK0) )
    | ~ spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f777,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f777,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v7_struct_0(sK0) )
    | ~ spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f776,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f776,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v7_struct_0(sK0) )
    | ~ spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f771,f59])).

fof(f771,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v7_struct_0(sK0) )
    | ~ spl5_5
    | spl5_7 ),
    inference(resolution,[],[f388,f536])).

fof(f388,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(X0),X2),u1_struct_0(X0))
      | v2_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f385,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f385,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(X0),X2),u1_struct_0(X0))
      | ~ v1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(resolution,[],[f197,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ sQ4_eqProxy(k6_domain_1(u1_struct_0(X0),X2),u1_struct_0(X0))
      | ~ v1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f161,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | ~ sQ4_eqProxy(k6_domain_1(X0,X1),X0)
      | ~ v1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f88,f65])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ sQ4_eqProxy(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f64,f87])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f161,plain,(
    ! [X4,X5] :
      ( m1_subset_1(u1_struct_0(k1_tex_2(X5,X4)),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | m1_subset_1(u1_struct_0(k1_tex_2(X5,X4)),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f82,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f260,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f259,f58])).

fof(f259,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f237,f68])).

fof(f237,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl5_5
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f536,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f533,f260])).

fof(f533,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_7 ),
    inference(resolution,[],[f528,f91])).

fof(f528,plain,
    ( ~ sQ4_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl5_7 ),
    inference(resolution,[],[f270,f110])).

fof(f270,plain,
    ( ~ sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl5_7
  <=> sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f478,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_8
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f57,f274,f58,f278,f237,f115,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f278,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl5_9
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f274,plain,
    ( v7_struct_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f272])).

fof(f475,plain,
    ( ~ spl5_2
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f57,f274,f59,f119,f459,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f459,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl5_15
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f469,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl5_15 ),
    inference(subsumption_resolution,[],[f466,f58])).

fof(f466,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_15 ),
    inference(resolution,[],[f460,f66])).

fof(f460,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f458])).

fof(f427,plain,
    ( spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f425,f58])).

fof(f425,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f424,f237])).

fof(f424,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f419,f114])).

fof(f114,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f419,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(resolution,[],[f330,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(u1_struct_0(X1),sK3(X0,X1))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f71,f87])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f330,plain,
    ( ~ sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),sK3(sK0,k1_tex_2(sK0,sK1)))
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f329,f109])).

fof(f109,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f87])).

fof(f329,plain,
    ( ~ sQ4_eqProxy(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),sK3(sK0,k1_tex_2(sK0,sK1)))
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(resolution,[],[f326,f241])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(X0,X1)
        | ~ sQ4_eqProxy(X1,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1))) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X0,X1)
        | ~ sQ4_eqProxy(X1,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f326,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f323,f260])).

fof(f323,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_7 ),
    inference(resolution,[],[f320,f91])).

fof(f320,plain,
    ( ~ sQ4_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl5_7 ),
    inference(resolution,[],[f270,f110])).

fof(f303,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f301,f57])).

fof(f301,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f300,f58])).

fof(f300,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f297,f59])).

fof(f297,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f279,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f279,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f277])).

fof(f275,plain,
    ( ~ spl5_7
    | spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f232,f145,f272,f268])).

fof(f145,plain,
    ( spl5_3
  <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f232,plain,
    ( v7_struct_0(sK0)
    | ~ sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f220,f58])).

fof(f220,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(X2)
        | v7_struct_0(X2)
        | ~ sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(X2)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f181,f66])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(X0))
        | v7_struct_0(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f180,f73])).

fof(f180,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(X0)
        | ~ sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f147,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ sQ4_eqProxy(X0,X1)
      | v1_zfmisc_1(X1) ) ),
    inference(equality_proxy_axiom,[],[f87])).

fof(f147,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f257,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f255,f109])).

fof(f255,plain,
    ( ~ sQ4_eqProxy(sK0,sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f247,f109])).

fof(f247,plain,
    ( ~ sQ4_eqProxy(k1_tex_2(sK0,sK1),k1_tex_2(sK0,sK1))
    | ~ sQ4_eqProxy(sK0,sK0)
    | spl5_5 ),
    inference(resolution,[],[f238,f213])).

fof(f213,plain,(
    ! [X6,X7] :
      ( m1_pre_topc(X7,X6)
      | ~ sQ4_eqProxy(k1_tex_2(sK0,sK1),X7)
      | ~ sQ4_eqProxy(sK0,X6) ) ),
    inference(subsumption_resolution,[],[f212,f57])).

fof(f212,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK0)
      | ~ sQ4_eqProxy(sK0,X6)
      | ~ sQ4_eqProxy(k1_tex_2(sK0,sK1),X7)
      | m1_pre_topc(X7,X6) ) ),
    inference(subsumption_resolution,[],[f211,f58])).

fof(f211,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ sQ4_eqProxy(sK0,X6)
      | ~ sQ4_eqProxy(k1_tex_2(sK0,sK1),X7)
      | m1_pre_topc(X7,X6) ) ),
    inference(resolution,[],[f159,f59])).

fof(f159,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sQ4_eqProxy(X1,X2)
      | ~ sQ4_eqProxy(k1_tex_2(X1,X0),X3)
      | m1_pre_topc(X3,X2) ) ),
    inference(resolution,[],[f82,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,X2)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X0,X1)
      | m1_pre_topc(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f87])).

fof(f238,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f236])).

fof(f242,plain,
    ( ~ spl5_5
    | spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f218,f113,f240,f236])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(X0,X1)
        | ~ sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1)))
        | ~ sQ4_eqProxy(X1,u1_struct_0(sK0))
        | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f216,f58])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(X0,X1)
        | ~ sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1)))
        | ~ sQ4_eqProxy(X1,u1_struct_0(sK0))
        | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
        | ~ l1_pre_topc(sK0) )
    | spl5_1 ),
    inference(resolution,[],[f139,f114])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tex_2(X3,X1)
      | ~ v1_subset_1(X2,X0)
      | ~ sQ4_eqProxy(X2,sK3(X1,X3))
      | ~ sQ4_eqProxy(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f100,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_subset_1(X1,X3)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ v1_subset_1(X0,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f87])).

fof(f176,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f174,plain,
    ( v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f173,f59])).

fof(f173,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f172,f58])).

fof(f172,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(resolution,[],[f156,f82])).

fof(f156,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1) )
    | spl5_4 ),
    inference(resolution,[],[f154,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f154,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl5_4 ),
    inference(resolution,[],[f151,f66])).

fof(f151,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_4
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f152,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f133,f149,f145])).

fof(f133,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(resolution,[],[f127,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f127,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f126,f57])).

fof(f126,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f58])).

fof(f125,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f84,f59])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f120,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f60,f117,f113])).

fof(f60,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:35:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (10393)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (10393)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f896,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f120,f152,f176,f242,f257,f275,f303,f427,f469,f475,f478,f883,f895])).
% 0.20/0.45  fof(f895,plain,(
% 0.20/0.45    ~spl5_1 | ~spl5_2),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f894])).
% 0.20/0.45  fof(f894,plain,(
% 0.20/0.45    $false | (~spl5_1 | ~spl5_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f884,f119])).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f117])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    spl5_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.45  fof(f884,plain,(
% 0.20/0.45    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f61,f115])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl5_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f113])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    spl5_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f15])).
% 0.20/0.45  fof(f15,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.20/0.45  fof(f883,plain,(
% 0.20/0.45    spl5_2 | ~spl5_5 | spl5_7 | spl5_8),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f875])).
% 0.20/0.45  fof(f875,plain,(
% 0.20/0.45    $false | (spl5_2 | ~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f536,f260,f867,f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.20/0.45  fof(f867,plain,(
% 0.20/0.45    v1_xboole_0(u1_struct_0(sK0)) | (spl5_2 | ~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(subsumption_resolution,[],[f865,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f47])).
% 0.20/0.45  fof(f865,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl5_2 | ~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(resolution,[],[f861,f80])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.45  fof(f861,plain,(
% 0.20/0.45    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_2 | ~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(subsumption_resolution,[],[f858,f118])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl5_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f117])).
% 0.20/0.45  fof(f858,plain,(
% 0.20/0.45    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(resolution,[],[f854,f91])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sQ4_eqProxy(X0,X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f79,f87])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.45    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.45  fof(f854,plain,(
% 0.20/0.45    ~sQ4_eqProxy(u1_struct_0(sK0),k6_domain_1(u1_struct_0(sK0),sK1)) | (~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(resolution,[],[f844,f110])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f87])).
% 0.20/0.45  fof(f844,plain,(
% 0.20/0.45    ~sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(resolution,[],[f779,f59])).
% 0.20/0.45  fof(f779,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))) ) | (~spl5_5 | spl5_7 | spl5_8)),
% 0.20/0.45    inference(subsumption_resolution,[],[f778,f273])).
% 0.20/0.45  fof(f273,plain,(
% 0.20/0.45    ~v7_struct_0(sK0) | spl5_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f272])).
% 0.20/0.45  fof(f272,plain,(
% 0.20/0.45    spl5_8 <=> v7_struct_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.45  fof(f778,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | v7_struct_0(sK0)) ) | (~spl5_5 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f777,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f47])).
% 0.20/0.45  fof(f777,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v7_struct_0(sK0)) ) | (~spl5_5 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f776,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f47])).
% 0.20/0.45  fof(f776,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v7_struct_0(sK0)) ) | (~spl5_5 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f771,f59])).
% 0.20/0.45  fof(f771,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v7_struct_0(sK0)) ) | (~spl5_5 | spl5_7)),
% 0.20/0.45    inference(resolution,[],[f388,f536])).
% 0.20/0.45  fof(f388,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(X0),X2),u1_struct_0(X0)) | v2_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f385,f66])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.45  fof(f385,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(X0),X2),u1_struct_0(X0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.45    inference(resolution,[],[f197,f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.20/0.45  fof(f197,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (v1_zfmisc_1(u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~sQ4_eqProxy(k6_domain_1(u1_struct_0(X0),X2),u1_struct_0(X0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),u1_struct_0(X0))) )),
% 0.20/0.45    inference(resolution,[],[f161,f122])).
% 0.20/0.45  fof(f122,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | ~sQ4_eqProxy(k6_domain_1(X0,X1),X0) | ~v1_subset_1(X2,X0)) )),
% 0.20/0.45    inference(resolution,[],[f88,f65])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_xboole_0(X0) | ~sQ4_eqProxy(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0)) )),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f64,f87])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(rectify,[],[f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.45  fof(f161,plain,(
% 0.20/0.45    ( ! [X4,X5] : (m1_subset_1(u1_struct_0(k1_tex_2(X5,X4)),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f160])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~l1_pre_topc(X5) | v2_struct_0(X5) | m1_subset_1(u1_struct_0(k1_tex_2(X5,X4)),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5)) )),
% 0.20/0.45    inference(resolution,[],[f82,f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.45  fof(f260,plain,(
% 0.20/0.45    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.20/0.45    inference(subsumption_resolution,[],[f259,f58])).
% 0.20/0.45  fof(f259,plain,(
% 0.20/0.45    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_5),
% 0.20/0.45    inference(resolution,[],[f237,f68])).
% 0.20/0.45  fof(f237,plain,(
% 0.20/0.45    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl5_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f236])).
% 0.20/0.45  fof(f236,plain,(
% 0.20/0.45    spl5_5 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.45  fof(f536,plain,(
% 0.20/0.45    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl5_5 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f533,f260])).
% 0.20/0.45  fof(f533,plain,(
% 0.20/0.45    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_7),
% 0.20/0.45    inference(resolution,[],[f528,f91])).
% 0.20/0.45  fof(f528,plain,(
% 0.20/0.45    ~sQ4_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))) | spl5_7),
% 0.20/0.45    inference(resolution,[],[f270,f110])).
% 0.20/0.45  fof(f270,plain,(
% 0.20/0.45    ~sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | spl5_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f268])).
% 0.20/0.45  fof(f268,plain,(
% 0.20/0.45    spl5_7 <=> sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.45  fof(f478,plain,(
% 0.20/0.45    ~spl5_1 | ~spl5_5 | ~spl5_8 | spl5_9),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f476])).
% 0.20/0.45  fof(f476,plain,(
% 0.20/0.45    $false | (~spl5_1 | ~spl5_5 | ~spl5_8 | spl5_9)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f57,f274,f58,f278,f237,f115,f76])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v7_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.20/0.45  fof(f278,plain,(
% 0.20/0.45    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl5_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f277])).
% 0.20/0.45  fof(f277,plain,(
% 0.20/0.45    spl5_9 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.45  fof(f274,plain,(
% 0.20/0.45    v7_struct_0(sK0) | ~spl5_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f272])).
% 0.20/0.45  fof(f475,plain,(
% 0.20/0.45    ~spl5_2 | ~spl5_8 | ~spl5_15),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f472])).
% 0.20/0.45  fof(f472,plain,(
% 0.20/0.45    $false | (~spl5_2 | ~spl5_8 | ~spl5_15)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f57,f274,f59,f119,f459,f74])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 0.20/0.45  fof(f459,plain,(
% 0.20/0.45    l1_struct_0(sK0) | ~spl5_15),
% 0.20/0.45    inference(avatar_component_clause,[],[f458])).
% 0.20/0.45  fof(f458,plain,(
% 0.20/0.45    spl5_15 <=> l1_struct_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.45  fof(f469,plain,(
% 0.20/0.45    spl5_15),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f468])).
% 0.20/0.45  fof(f468,plain,(
% 0.20/0.45    $false | spl5_15),
% 0.20/0.45    inference(subsumption_resolution,[],[f466,f58])).
% 0.20/0.45  fof(f466,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | spl5_15),
% 0.20/0.45    inference(resolution,[],[f460,f66])).
% 0.20/0.45  fof(f460,plain,(
% 0.20/0.45    ~l1_struct_0(sK0) | spl5_15),
% 0.20/0.45    inference(avatar_component_clause,[],[f458])).
% 0.20/0.45  fof(f427,plain,(
% 0.20/0.45    spl5_1 | ~spl5_5 | ~spl5_6 | spl5_7),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f426])).
% 0.20/0.45  fof(f426,plain,(
% 0.20/0.45    $false | (spl5_1 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f425,f58])).
% 0.20/0.45  fof(f425,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f424,f237])).
% 0.20/0.45  fof(f424,plain,(
% 0.20/0.45    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f419,f114])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl5_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f113])).
% 0.20/0.45  fof(f419,plain,(
% 0.20/0.45    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl5_5 | ~spl5_6 | spl5_7)),
% 0.20/0.45    inference(resolution,[],[f330,f90])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sQ4_eqProxy(u1_struct_0(X1),sK3(X0,X1)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f71,f87])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(rectify,[],[f52])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.45  fof(f330,plain,(
% 0.20/0.45    ~sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),sK3(sK0,k1_tex_2(sK0,sK1))) | (~spl5_5 | ~spl5_6 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f329,f109])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f87])).
% 0.20/0.45  fof(f329,plain,(
% 0.20/0.45    ~sQ4_eqProxy(u1_struct_0(sK0),u1_struct_0(sK0)) | ~sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),sK3(sK0,k1_tex_2(sK0,sK1))) | (~spl5_5 | ~spl5_6 | spl5_7)),
% 0.20/0.45    inference(resolution,[],[f326,f241])).
% 0.20/0.45  fof(f241,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_subset_1(X0,X1) | ~sQ4_eqProxy(X1,u1_struct_0(sK0)) | ~sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1)))) ) | ~spl5_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f240])).
% 0.20/0.45  fof(f240,plain,(
% 0.20/0.45    spl5_6 <=> ! [X1,X0] : (~v1_subset_1(X0,X1) | ~sQ4_eqProxy(X1,u1_struct_0(sK0)) | ~sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.45  fof(f326,plain,(
% 0.20/0.45    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl5_5 | spl5_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f323,f260])).
% 0.20/0.45  fof(f323,plain,(
% 0.20/0.45    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_7),
% 0.20/0.45    inference(resolution,[],[f320,f91])).
% 0.20/0.45  fof(f320,plain,(
% 0.20/0.45    ~sQ4_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))) | spl5_7),
% 0.20/0.45    inference(resolution,[],[f270,f110])).
% 0.20/0.45  fof(f303,plain,(
% 0.20/0.45    ~spl5_9),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f302])).
% 0.20/0.45  fof(f302,plain,(
% 0.20/0.45    $false | ~spl5_9),
% 0.20/0.45    inference(subsumption_resolution,[],[f301,f57])).
% 0.20/0.45  fof(f301,plain,(
% 0.20/0.45    v2_struct_0(sK0) | ~spl5_9),
% 0.20/0.45    inference(subsumption_resolution,[],[f300,f58])).
% 0.20/0.45  fof(f300,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_9),
% 0.20/0.45    inference(subsumption_resolution,[],[f297,f59])).
% 0.20/0.45  fof(f297,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_9),
% 0.20/0.45    inference(resolution,[],[f279,f81])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f40])).
% 0.20/0.45  fof(f279,plain,(
% 0.20/0.45    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f277])).
% 0.20/0.45  fof(f275,plain,(
% 0.20/0.45    ~spl5_7 | spl5_8 | ~spl5_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f232,f145,f272,f268])).
% 0.20/0.45  fof(f145,plain,(
% 0.20/0.45    spl5_3 <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.45  fof(f232,plain,(
% 0.20/0.45    v7_struct_0(sK0) | ~sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl5_3),
% 0.20/0.45    inference(resolution,[],[f220,f58])).
% 0.20/0.45  fof(f220,plain,(
% 0.20/0.45    ( ! [X2] : (~l1_pre_topc(X2) | v7_struct_0(X2) | ~sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(X2))) ) | ~spl5_3),
% 0.20/0.45    inference(resolution,[],[f181,f66])).
% 0.20/0.45  fof(f181,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_struct_0(X0) | ~sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(X0)) | v7_struct_0(X0)) ) | ~spl5_3),
% 0.20/0.45    inference(resolution,[],[f180,f73])).
% 0.20/0.45  fof(f180,plain,(
% 0.20/0.45    ( ! [X0] : (v1_zfmisc_1(X0) | ~sQ4_eqProxy(u1_struct_0(k1_tex_2(sK0,sK1)),X0)) ) | ~spl5_3),
% 0.20/0.45    inference(resolution,[],[f147,f105])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~sQ4_eqProxy(X0,X1) | v1_zfmisc_1(X1)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f87])).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f145])).
% 0.20/0.45  fof(f257,plain,(
% 0.20/0.45    spl5_5),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.45  fof(f256,plain,(
% 0.20/0.45    $false | spl5_5),
% 0.20/0.45    inference(subsumption_resolution,[],[f255,f109])).
% 0.20/0.45  fof(f255,plain,(
% 0.20/0.45    ~sQ4_eqProxy(sK0,sK0) | spl5_5),
% 0.20/0.45    inference(subsumption_resolution,[],[f247,f109])).
% 0.20/0.45  fof(f247,plain,(
% 0.20/0.45    ~sQ4_eqProxy(k1_tex_2(sK0,sK1),k1_tex_2(sK0,sK1)) | ~sQ4_eqProxy(sK0,sK0) | spl5_5),
% 0.20/0.45    inference(resolution,[],[f238,f213])).
% 0.20/0.45  fof(f213,plain,(
% 0.20/0.45    ( ! [X6,X7] : (m1_pre_topc(X7,X6) | ~sQ4_eqProxy(k1_tex_2(sK0,sK1),X7) | ~sQ4_eqProxy(sK0,X6)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f212,f57])).
% 0.20/0.45  fof(f212,plain,(
% 0.20/0.45    ( ! [X6,X7] : (v2_struct_0(sK0) | ~sQ4_eqProxy(sK0,X6) | ~sQ4_eqProxy(k1_tex_2(sK0,sK1),X7) | m1_pre_topc(X7,X6)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f211,f58])).
% 0.20/0.45  fof(f211,plain,(
% 0.20/0.45    ( ! [X6,X7] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~sQ4_eqProxy(sK0,X6) | ~sQ4_eqProxy(k1_tex_2(sK0,sK1),X7) | m1_pre_topc(X7,X6)) )),
% 0.20/0.45    inference(resolution,[],[f159,f59])).
% 0.20/0.45  fof(f159,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~sQ4_eqProxy(X1,X2) | ~sQ4_eqProxy(k1_tex_2(X1,X0),X3) | m1_pre_topc(X3,X2)) )),
% 0.20/0.45    inference(resolution,[],[f82,f103])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X2) | ~sQ4_eqProxy(X2,X3) | ~sQ4_eqProxy(X0,X1) | m1_pre_topc(X1,X3)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f87])).
% 0.20/0.45  fof(f238,plain,(
% 0.20/0.45    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | spl5_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f236])).
% 0.20/0.45  fof(f242,plain,(
% 0.20/0.45    ~spl5_5 | spl5_6 | spl5_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f218,f113,f240,f236])).
% 0.20/0.45  fof(f218,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_subset_1(X0,X1) | ~sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1))) | ~sQ4_eqProxy(X1,u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0)) ) | spl5_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f216,f58])).
% 0.20/0.45  fof(f216,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_subset_1(X0,X1) | ~sQ4_eqProxy(X0,sK3(sK0,k1_tex_2(sK0,sK1))) | ~sQ4_eqProxy(X1,u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)) ) | spl5_1),
% 0.20/0.45    inference(resolution,[],[f139,f114])).
% 0.20/0.45  fof(f139,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (v1_tex_2(X3,X1) | ~v1_subset_1(X2,X0) | ~sQ4_eqProxy(X2,sK3(X1,X3)) | ~sQ4_eqProxy(X0,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.45    inference(resolution,[],[f100,f72])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f55])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (v1_subset_1(X1,X3) | ~sQ4_eqProxy(X2,X3) | ~v1_subset_1(X0,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f87])).
% 0.20/0.45  fof(f176,plain,(
% 0.20/0.45    spl5_4),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.45  fof(f175,plain,(
% 0.20/0.45    $false | spl5_4),
% 0.20/0.45    inference(subsumption_resolution,[],[f174,f57])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    v2_struct_0(sK0) | spl5_4),
% 0.20/0.46    inference(subsumption_resolution,[],[f173,f59])).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl5_4),
% 0.20/0.46    inference(subsumption_resolution,[],[f172,f58])).
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl5_4),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f171])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_4),
% 0.20/0.46    inference(resolution,[],[f156,f82])).
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    ( ! [X1] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X1) | ~l1_pre_topc(X1)) ) | spl5_4),
% 0.20/0.46    inference(resolution,[],[f154,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl5_4),
% 0.20/0.46    inference(resolution,[],[f151,f66])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl5_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f149])).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    spl5_4 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    spl5_3 | ~spl5_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f133,f149,f145])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.46    inference(resolution,[],[f127,f77])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.20/0.46  fof(f127,plain,(
% 0.20/0.46    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.46    inference(subsumption_resolution,[],[f126,f57])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f125,f58])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(resolution,[],[f84,f59])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.46  fof(f13,axiom,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    spl5_1 | spl5_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f60,f117,f113])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f47])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (10393)------------------------------
% 0.20/0.46  % (10393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (10393)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (10393)Memory used [KB]: 6652
% 0.20/0.46  % (10393)Time elapsed: 0.043 s
% 0.20/0.46  % (10393)------------------------------
% 0.20/0.46  % (10393)------------------------------
% 0.20/0.46  % (10385)Success in time 0.105 s
%------------------------------------------------------------------------------
