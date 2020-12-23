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
% DateTime   : Thu Dec  3 13:13:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 275 expanded)
%              Number of leaves         :   30 ( 125 expanded)
%              Depth                    :    9
%              Number of atoms          :  399 (1073 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f56,f61,f66,f71,f76,f82,f88,f94,f100,f108,f112,f125,f131,f138,f153,f163,f173,f178,f184,f185])).

fof(f185,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v4_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f184,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

% (6953)Termination reason: Refutation not found, incomplete strategy

% (6953)Memory used [KB]: 10618
% (6953)Time elapsed: 0.050 s
% (6953)------------------------------
% (6953)------------------------------
fof(f178,plain,
    ( spl2_19
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f155,f91,f79,f73,f175])).

fof(f175,plain,
    ( spl2_19
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f73,plain,
    ( spl2_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f79,plain,
    ( spl2_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f91,plain,
    ( spl2_9
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f155,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f75,f93,f81,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f81,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f173,plain,
    ( spl2_18
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f156,f97,f79,f73,f170])).

fof(f170,plain,
    ( spl2_18
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f97,plain,
    ( spl2_10
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f156,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f75,f99,f81,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f99,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f163,plain,
    ( spl2_16
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f158,f79,f160])).

fof(f160,plain,
    ( spl2_16
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f158,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f153,plain,
    ( ~ spl2_6
    | ~ spl2_14
    | ~ spl2_15
    | spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f143,f127,f105,f149,f145,f73])).

fof(f145,plain,
    ( spl2_14
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f149,plain,
    ( spl2_15
  <=> v4_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f105,plain,
    ( spl2_11
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f127,plain,
    ( spl2_12
  <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f143,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v4_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_12 ),
    inference(superposition,[],[f44,f129])).

fof(f129,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f138,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f132,f73,f68,f135])).

fof(f135,plain,
    ( spl2_13
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f68,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f132,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f75,f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f131,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f113,f73,f68,f48,f127])).

fof(f48,plain,
    ( spl2_1
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f113,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f75,f70,f49,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f49,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f125,plain,
    ( ~ spl2_6
    | ~ spl2_5
    | ~ spl2_11
    | spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f121,f85,f52,f105,f68,f73])).

fof(f52,plain,
    ( spl2_2
  <=> v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_8
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f121,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f118,f87])).

fof(f87,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f85])).

% (6931)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f118,plain,
    ( sK1 != k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2 ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f54,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f112,plain,
    ( ~ spl2_8
    | spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f111,f105,f73,f68,f48,f85])).

fof(f111,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f109,f107])).

fof(f107,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f109,plain,
    ( sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f75,f50,f70,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f108,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f103,f85,f73,f68,f52,f105])).

fof(f103,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f101,f87])).

fof(f101,plain,
    ( sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f75,f53,f70,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f100,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f95,f73,f68,f63,f97])).

fof(f63,plain,
    ( spl2_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f95,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f75,f65,f70,f42])).

fof(f65,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f63])).

% (6930)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% (6937)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (6943)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (6935)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% (6938)Refutation not found, incomplete strategy% (6938)------------------------------
% (6938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6941)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (6950)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (6938)Termination reason: Refutation not found, incomplete strategy

% (6938)Memory used [KB]: 10618
% (6938)Time elapsed: 0.094 s
% (6938)------------------------------
% (6938)------------------------------
% (6951)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (6944)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (6942)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f94,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f89,f73,f68,f58,f91])).

fof(f58,plain,
    ( spl2_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f89,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f75,f60,f70,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f60,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f88,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f83,f73,f68,f58,f85])).

fof(f83,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f75,f60,f70,f44])).

fof(f82,plain,
    ( spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f77,f68,f79])).

fof(f77,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f70,f45])).

fof(f76,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ v6_tops_1(sK1,sK0)
      | ~ v5_tops_1(sK1,sK0) )
    & ( v6_tops_1(sK1,sK0)
      | v5_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v6_tops_1(X1,X0)
              | ~ v5_tops_1(X1,X0) )
            & ( v6_tops_1(X1,X0)
              | v5_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v6_tops_1(X1,sK0)
            | ~ v5_tops_1(X1,sK0) )
          & ( v6_tops_1(X1,sK0)
            | v5_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ( ~ v6_tops_1(X1,sK0)
          | ~ v5_tops_1(X1,sK0) )
        & ( v6_tops_1(X1,sK0)
          | v5_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v6_tops_1(sK1,sK0)
        | ~ v5_tops_1(sK1,sK0) )
      & ( v6_tops_1(sK1,sK0)
        | v5_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v3_pre_topc(X1,X0) )
             => ( v5_tops_1(X1,X0)
              <=> v6_tops_1(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0) )
           => ( v5_tops_1(X1,X0)
            <=> v6_tops_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).

fof(f71,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f34,f52,f48])).

fof(f34,plain,
    ( v6_tops_1(sK1,sK0)
    | v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f35,f52,f48])).

fof(f35,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:32:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (6933)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (6939)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (6938)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (6932)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (6953)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (6945)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (6934)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (6936)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (6949)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (6947)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (6953)Refutation not found, incomplete strategy% (6953)------------------------------
% 0.22/0.51  % (6953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6948)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (6933)Refutation not found, incomplete strategy% (6933)------------------------------
% 0.22/0.51  % (6933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6933)Memory used [KB]: 10618
% 0.22/0.51  % (6933)Time elapsed: 0.085 s
% 0.22/0.51  % (6936)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (6933)------------------------------
% 0.22/0.51  % (6933)------------------------------
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f55,f56,f61,f66,f71,f76,f82,f88,f94,f100,f108,f112,f125,f131,f138,f153,f163,f173,f178,f184,f185])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | v4_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  % (6953)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6953)Memory used [KB]: 10618
% 0.22/0.51  % (6953)Time elapsed: 0.050 s
% 0.22/0.51  % (6953)------------------------------
% 0.22/0.51  % (6953)------------------------------
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    spl2_19 | ~spl2_6 | ~spl2_7 | ~spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f91,f79,f73,f175])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    spl2_19 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl2_6 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl2_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl2_9 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl2_6 | ~spl2_7 | ~spl2_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f75,f93,f81,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl2_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f73])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl2_18 | ~spl2_6 | ~spl2_7 | ~spl2_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f156,f97,f79,f73,f170])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl2_18 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl2_10 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_6 | ~spl2_7 | ~spl2_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f75,f99,f81,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    spl2_16 | ~spl2_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f158,f79,f160])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl2_16 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f81,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ~spl2_6 | ~spl2_14 | ~spl2_15 | spl2_11 | ~spl2_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f143,f127,f105,f149,f145,f73])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    spl2_14 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    spl2_15 <=> v4_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl2_11 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl2_12 <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    sK1 = k1_tops_1(sK0,sK1) | ~v4_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_12),
% 0.22/0.51    inference(superposition,[],[f44,f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~spl2_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    spl2_13 | ~spl2_5 | ~spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f132,f73,f68,f135])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl2_13 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_5 | ~spl2_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f75,f70,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f68])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl2_12 | ~spl2_1 | ~spl2_5 | ~spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f113,f73,f68,f48,f127])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl2_1 <=> v5_tops_1(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_5 | ~spl2_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f75,f70,f49,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v5_tops_1(sK1,sK0) | ~spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f48])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~spl2_6 | ~spl2_5 | ~spl2_11 | spl2_2 | ~spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f121,f85,f52,f105,f68,f73])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl2_2 <=> v6_tops_1(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl2_8 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    sK1 != k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_8)),
% 0.22/0.51    inference(forward_demodulation,[],[f118,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  % (6931)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    sK1 != k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_2),
% 0.22/0.51    inference(resolution,[],[f54,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ~v6_tops_1(sK1,sK0) | spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f52])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ~spl2_8 | spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f111,f105,f73,f68,f48,f85])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    sK1 != k2_pre_topc(sK0,sK1) | (spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_11)),
% 0.22/0.51    inference(forward_demodulation,[],[f109,f107])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    sK1 = k1_tops_1(sK0,sK1) | ~spl2_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f105])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (spl2_1 | ~spl2_5 | ~spl2_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f75,f50,f70,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~v5_tops_1(sK1,sK0) | spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f48])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl2_11 | ~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f103,f85,f73,f68,f52,f105])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    sK1 = k1_tops_1(sK0,sK1) | (~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_8)),
% 0.22/0.51    inference(forward_demodulation,[],[f101,f87])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f75,f53,f70,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    v6_tops_1(sK1,sK0) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f52])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl2_10 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f95,f73,f68,f63,f97])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl2_4 <=> v3_pre_topc(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f75,f65,f70,f42])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0) | ~spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f63])).
% 0.22/0.51  % (6930)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (6937)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (6943)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (6935)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (6938)Refutation not found, incomplete strategy% (6938)------------------------------
% 0.22/0.51  % (6938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6941)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (6950)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (6938)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6938)Memory used [KB]: 10618
% 0.22/0.52  % (6938)Time elapsed: 0.094 s
% 0.22/0.52  % (6938)------------------------------
% 0.22/0.52  % (6938)------------------------------
% 0.22/0.52  % (6951)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (6944)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (6942)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl2_9 | ~spl2_3 | ~spl2_5 | ~spl2_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f89,f73,f68,f58,f91])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl2_3 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f75,f60,f70,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    v4_pre_topc(sK1,sK0) | ~spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f58])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    spl2_8 | ~spl2_3 | ~spl2_5 | ~spl2_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f83,f73,f68,f58,f85])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_5 | ~spl2_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f75,f60,f70,f44])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl2_7 | ~spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f77,f68,f79])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f70,f45])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl2_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f73])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f68])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl2_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f63])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    v3_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f58])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    v4_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl2_1 | spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f52,f48])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ~spl2_1 | ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f52,f48])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (6936)------------------------------
% 0.22/0.53  % (6936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6936)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (6936)Memory used [KB]: 10746
% 0.22/0.53  % (6936)Time elapsed: 0.090 s
% 0.22/0.53  % (6936)------------------------------
% 0.22/0.53  % (6936)------------------------------
% 0.22/0.53  % (6929)Success in time 0.16 s
%------------------------------------------------------------------------------
