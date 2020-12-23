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
% DateTime   : Thu Dec  3 13:20:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 149 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  254 ( 503 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f56,f60,f64,f68,f74,f81,f86,f94,f108,f111,f115])).

fof(f115,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl2_4
    | spl2_5
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f113,f51])).

fof(f51,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f113,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f112,f46])).

fof(f46,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f112,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(resolution,[],[f104,f63])).

% (6522)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
fof(f63,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f104,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_15
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f111,plain,
    ( ~ spl2_11
    | ~ spl2_12
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f109,f85])).

fof(f85,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_12
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f109,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(resolution,[],[f107,f80])).

fof(f80,plain,
    ( v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_11
  <=> v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f107,plain,
    ( ! [X2] :
        ( ~ v1_subset_1(k6_domain_1(k2_struct_0(sK0),X2),k2_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_struct_0(sK0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl2_16
  <=> ! [X2] :
        ( ~ v1_subset_1(k6_domain_1(k2_struct_0(sK0),X2),k2_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f108,plain,
    ( spl2_15
    | spl2_16
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f96,f91,f54,f106,f102])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( ~ v1_zfmisc_1(X0)
        | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f91,plain,
    ( spl2_13
  <=> v1_zfmisc_1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f96,plain,
    ( ! [X2] :
        ( ~ v1_subset_1(k6_domain_1(k2_struct_0(sK0),X2),k2_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_struct_0(sK0))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(resolution,[],[f55,f93])).

fof(f93,plain,
    ( v1_zfmisc_1(k2_struct_0(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_zfmisc_1(X0)
        | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f94,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f89,f71,f66,f44,f29,f91])).

fof(f29,plain,
    ( spl2_1
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X0] :
        ( v1_zfmisc_1(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | ~ v7_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f71,plain,
    ( spl2_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f89,plain,
    ( v1_zfmisc_1(k2_struct_0(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f31,plain,
    ( v7_struct_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f88,plain,
    ( v1_zfmisc_1(k2_struct_0(sK0))
    | ~ v7_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,
    ( v1_zfmisc_1(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(superposition,[],[f67,f73])).

fof(f73,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f67,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | ~ v7_struct_0(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f86,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f76,f71,f39,f83])).

fof(f39,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f76,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f41,f73])).

fof(f41,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f81,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f75,f71,f34,f78])).

fof(f34,plain,
    ( spl2_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f75,plain,
    ( v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(superposition,[],[f36,f73])).

fof(f36,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f74,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f69,f58,f44,f71])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f69,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f52,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( v7_struct_0(sK0)
    & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v7_struct_0(X0)
            & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v7_struct_0(sK0)
          & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( v7_struct_0(sK0)
        & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( v7_struct_0(sK0)
      & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ ( v7_struct_0(X0)
                & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f34])).

fof(f22,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f29])).

fof(f23,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (6521)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (6520)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (6519)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (6513)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.44  % (6518)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (6517)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (6518)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f56,f60,f64,f68,f74,f81,f86,f94,f108,f111,f115])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    ~spl2_4 | spl2_5 | ~spl2_8 | ~spl2_15),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f114])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    $false | (~spl2_4 | spl2_5 | ~spl2_8 | ~spl2_15)),
% 0.22/0.44    inference(subsumption_resolution,[],[f113,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ~v2_struct_0(sK0) | spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl2_5 <=> v2_struct_0(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f113,plain,(
% 0.22/0.44    v2_struct_0(sK0) | (~spl2_4 | ~spl2_8 | ~spl2_15)),
% 0.22/0.44    inference(subsumption_resolution,[],[f112,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    l1_struct_0(sK0) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl2_4 <=> l1_struct_0(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f112,plain,(
% 0.22/0.44    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl2_8 | ~spl2_15)),
% 0.22/0.44    inference(resolution,[],[f104,f63])).
% 0.22/0.44  % (6522)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl2_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl2_8 <=> ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    v1_xboole_0(k2_struct_0(sK0)) | ~spl2_15),
% 0.22/0.44    inference(avatar_component_clause,[],[f102])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    spl2_15 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.44  fof(f111,plain,(
% 0.22/0.44    ~spl2_11 | ~spl2_12 | ~spl2_16),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.44  fof(f110,plain,(
% 0.22/0.44    $false | (~spl2_11 | ~spl2_12 | ~spl2_16)),
% 0.22/0.44    inference(subsumption_resolution,[],[f109,f85])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl2_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f83])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    spl2_12 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.44  fof(f109,plain,(
% 0.22/0.44    ~m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl2_11 | ~spl2_16)),
% 0.22/0.44    inference(resolution,[],[f107,f80])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl2_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f78])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl2_11 <=> v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    ( ! [X2] : (~v1_subset_1(k6_domain_1(k2_struct_0(sK0),X2),k2_struct_0(sK0)) | ~m1_subset_1(X2,k2_struct_0(sK0))) ) | ~spl2_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f106])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    spl2_16 <=> ! [X2] : (~v1_subset_1(k6_domain_1(k2_struct_0(sK0),X2),k2_struct_0(sK0)) | ~m1_subset_1(X2,k2_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    spl2_15 | spl2_16 | ~spl2_6 | ~spl2_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f96,f91,f54,f106,f102])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    spl2_6 <=> ! [X1,X0] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    spl2_13 <=> v1_zfmisc_1(k2_struct_0(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    ( ! [X2] : (~v1_subset_1(k6_domain_1(k2_struct_0(sK0),X2),k2_struct_0(sK0)) | ~m1_subset_1(X2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl2_6 | ~spl2_13)),
% 0.22/0.44    inference(resolution,[],[f55,f93])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    v1_zfmisc_1(k2_struct_0(sK0)) | ~spl2_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f91])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f54])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    spl2_13 | ~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f89,f71,f66,f44,f29,f91])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl2_1 <=> v7_struct_0(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl2_9 <=> ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl2_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    v1_zfmisc_1(k2_struct_0(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f88,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    v7_struct_0(sK0) | ~spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f29])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    v1_zfmisc_1(k2_struct_0(sK0)) | ~v7_struct_0(sK0) | (~spl2_4 | ~spl2_9 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f87,f46])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    v1_zfmisc_1(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | (~spl2_9 | ~spl2_10)),
% 0.22/0.44    inference(superposition,[],[f67,f73])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f71])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) ) | ~spl2_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f66])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    spl2_12 | ~spl2_3 | ~spl2_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f76,f71,f39,f83])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl2_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl2_3 | ~spl2_10)),
% 0.22/0.44    inference(superposition,[],[f41,f73])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f39])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    spl2_11 | ~spl2_2 | ~spl2_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f75,f71,f34,f78])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl2_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | (~spl2_2 | ~spl2_10)),
% 0.22/0.44    inference(superposition,[],[f36,f73])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f34])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl2_10 | ~spl2_4 | ~spl2_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f69,f58,f44,f71])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl2_7 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl2_4 | ~spl2_7)),
% 0.22/0.44    inference(resolution,[],[f59,f46])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl2_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f58])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl2_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f66])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl2_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f62])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl2_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f58])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl2_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f54])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ~spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f19,f49])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ~v2_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ? [X1] : (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.45    inference(negated_conjecture,[],[f5])).
% 0.22/0.45  fof(f5,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f44])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    l1_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f39])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f34])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f29])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    v7_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (6518)------------------------------
% 0.22/0.45  % (6518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (6518)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (6518)Memory used [KB]: 10618
% 0.22/0.45  % (6518)Time elapsed: 0.037 s
% 0.22/0.45  % (6518)------------------------------
% 0.22/0.45  % (6518)------------------------------
% 0.22/0.45  % (6512)Success in time 0.089 s
%------------------------------------------------------------------------------
