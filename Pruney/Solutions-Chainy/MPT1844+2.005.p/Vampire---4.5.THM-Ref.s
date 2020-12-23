%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 138 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  237 ( 451 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f79,f87,f99,f112,f119,f136])).

fof(f136,plain,
    ( ~ spl5_2
    | spl5_7
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl5_2
    | spl5_7
    | spl5_11 ),
    inference(subsumption_resolution,[],[f134,f86])).

fof(f86,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_7
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f134,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl5_2
    | spl5_11 ),
    inference(subsumption_resolution,[],[f124,f55])).

fof(f55,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f124,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl5_11 ),
    inference(resolution,[],[f45,f118])).

fof(f118,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_11
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f119,plain,
    ( ~ spl5_11
    | spl5_1
    | spl5_10 ),
    inference(avatar_split_clause,[],[f113,f109,f48,f116])).

fof(f48,plain,
    ( spl5_1
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( spl5_10
  <=> u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f113,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_1
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f50,f111,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f111,plain,
    ( u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f50,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f112,plain,
    ( ~ spl5_10
    | ~ spl5_2
    | spl5_9 ),
    inference(avatar_split_clause,[],[f106,f96,f53,f109])).

fof(f96,plain,
    ( spl5_9
  <=> sP0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f106,plain,
    ( u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK3)
    | ~ spl5_2
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f55,f98,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) != X0
      | sP0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ( k6_domain_1(X0,sK4(X0)) = X0
          & m1_subset_1(sK4(X0),X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK4(X0)) = X0
        & m1_subset_1(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X2] :
            ( k6_domain_1(X0,X2) = X0
            & m1_subset_1(X2,X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ? [X1] :
          ( k6_domain_1(X0,X1) = X0
          & m1_subset_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f98,plain,
    ( ~ sP0(u1_struct_0(sK2))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f99,plain,
    ( ~ spl5_9
    | spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f88,f84,f76,f96])).

fof(f76,plain,
    ( spl5_6
  <=> v1_zfmisc_1(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f88,plain,
    ( ~ sP0(u1_struct_0(sK2))
    | spl5_6
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f78,f86,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f36,f40])).

fof(f40,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f10,f19,f18])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f36,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_zfmisc_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f78,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f87,plain,
    ( ~ spl5_7
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f82,f68,f58,f84])).

fof(f58,plain,
    ( spl5_3
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( spl5_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f82,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl5_3
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f70,f60,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f60,plain,
    ( l1_struct_0(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f79,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f74,f63,f58,f76])).

fof(f63,plain,
    ( spl5_4
  <=> v7_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f74,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f65,f60,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f65,plain,
    ( ~ v7_struct_0(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f71,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f30,f68])).

% (12807)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_struct_0(sK2)
    & ~ v7_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_struct_0(sK2)
      & ~ v7_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(f66,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ~ v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f34,f48])).

fof(f34,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (12805)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (12805)Refutation not found, incomplete strategy% (12805)------------------------------
% 0.20/0.47  % (12805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12799)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (12809)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (12805)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (12805)Memory used [KB]: 6140
% 0.20/0.47  % (12805)Time elapsed: 0.051 s
% 0.20/0.47  % (12805)------------------------------
% 0.20/0.47  % (12805)------------------------------
% 0.20/0.48  % (12809)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f79,f87,f99,f112,f119,f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ~spl5_2 | spl5_7 | spl5_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    $false | (~spl5_2 | spl5_7 | spl5_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f134,f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | spl5_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl5_7 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK2)) | (~spl5_2 | spl5_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f124,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl5_2 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ~m1_subset_1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | spl5_11),
% 0.20/0.48    inference(resolution,[],[f45,f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | spl5_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f116])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    spl5_11 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ~spl5_11 | spl5_1 | spl5_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f113,f109,f48,f116])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl5_1 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl5_10 <=> u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK2),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) | (spl5_1 | spl5_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f50,f111,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK3) | spl5_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f109])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~spl5_10 | ~spl5_2 | spl5_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f106,f96,f53,f109])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl5_9 <=> sP0(u1_struct_0(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK3) | (~spl5_2 | spl5_9)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f55,f98,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k6_domain_1(X0,X1) != X0 | sP0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)) | ~sP0(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~sP0(X0)))),
% 0.20/0.48    inference(rectify,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~sP0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (sP0(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~sP0(u1_struct_0(sK2)) | spl5_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f96])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ~spl5_9 | spl5_6 | spl5_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f88,f84,f76,f96])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl5_6 <=> v1_zfmisc_1(u1_struct_0(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ~sP0(u1_struct_0(sK2)) | (spl5_6 | spl5_7)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f78,f86,f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X0] : (~sP0(X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(resolution,[],[f36,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0] : (sP1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (sP1(X0) | v1_xboole_0(X0))),
% 0.20/0.48    inference(definition_folding,[],[f10,f19,f18])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : ((v1_zfmisc_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v1_zfmisc_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (((v1_zfmisc_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_zfmisc_1(X0))) | ~sP1(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~v1_zfmisc_1(u1_struct_0(sK2)) | spl5_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f76])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ~spl5_7 | ~spl5_3 | spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f82,f68,f58,f84])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl5_3 <=> l1_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl5_5 <=> v2_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | (~spl5_3 | spl5_5)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f70,f60,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    l1_struct_0(sK2) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f58])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ~v2_struct_0(sK2) | spl5_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f68])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ~spl5_6 | ~spl5_3 | spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f74,f63,f58,f76])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl5_4 <=> v7_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~v1_zfmisc_1(u1_struct_0(sK2)) | (~spl5_3 | spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f65,f60,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ~v7_struct_0(sK2) | spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f68])).
% 0.20/0.48  % (12807)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~v2_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    (~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_struct_0(sK2) & ~v7_struct_0(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f22,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_struct_0(sK2) & ~v7_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) => (~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ~spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f63])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ~v7_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f58])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    l1_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f53])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ~spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f48])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (12809)------------------------------
% 0.20/0.48  % (12809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (12809)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (12809)Memory used [KB]: 10618
% 0.20/0.48  % (12809)Time elapsed: 0.064 s
% 0.20/0.48  % (12809)------------------------------
% 0.20/0.48  % (12809)------------------------------
% 0.20/0.48  % (12788)Success in time 0.122 s
%------------------------------------------------------------------------------
