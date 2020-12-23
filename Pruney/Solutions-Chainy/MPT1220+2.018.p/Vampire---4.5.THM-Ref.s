%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 201 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 488 expanded)
%              Number of equality atoms :   59 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f55,f69,f75,f80,f85,f93,f101,f118,f124,f134,f135])).

% (9455)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f135,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) != k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) != k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f134,plain,
    ( spl1_14
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f109,f99,f83,f73,f53,f43,f132])).

fof(f132,plain,
    ( spl1_14
  <=> k2_pre_topc(sK0,k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f43,plain,
    ( spl1_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f53,plain,
    ( spl1_4
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f73,plain,
    ( spl1_6
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f83,plain,
    ( spl1_8
  <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f99,plain,
    ( spl1_10
  <=> m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f109,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f108,f76])).

fof(f76,plain,
    ( ! [X0] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = k4_xboole_0(k2_struct_0(sK0),X0)
    | ~ spl1_6 ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f74,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f108,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f107,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_8 ),
    inference(resolution,[],[f84,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

% (9454)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f84,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f107,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))))
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f102,f76])).

fof(f102,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))))
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_10 ),
    inference(resolution,[],[f100,f65])).

fof(f65,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3)) = X3 )
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f60,f44])).

fof(f44,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f60,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3)) = X3 )
    | ~ spl1_4 ),
    inference(superposition,[],[f26,f54])).

fof(f54,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(f100,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f124,plain,
    ( spl1_12
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f119,f116,f73,f122])).

fof(f122,plain,
    ( spl1_12
  <=> k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f116,plain,
    ( spl1_11
  <=> k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f119,plain,
    ( k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(superposition,[],[f117,f76])).

fof(f117,plain,
    ( k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f118,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f97,f91,f73,f53,f43,f116])).

fof(f91,plain,
    ( spl1_9
  <=> k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f97,plain,
    ( k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f96,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f96,plain,
    ( k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f95,f76])).

fof(f95,plain,
    ( k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(resolution,[],[f65,f74])).

fof(f101,plain,
    ( spl1_10
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f89,f73,f53,f38,f99])).

fof(f38,plain,
    ( spl1_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f89,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(resolution,[],[f64,f74])).

fof(f64,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f59,f39])).

fof(f39,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f38])).

% (9450)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f59,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl1_4 ),
    inference(superposition,[],[f28,f54])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f93,plain,
    ( spl1_9
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f86,f78,f73,f91])).

fof(f78,plain,
    ( spl1_7
  <=> k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f86,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(superposition,[],[f76,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f85,plain,
    ( spl1_8
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f81,f73,f53,f38,f83])).

fof(f81,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(resolution,[],[f63,f74])).

fof(f63,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(X1,k2_pre_topc(sK0,X1)) )
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f58,f39])).

fof(f58,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | r1_tarski(X1,k2_pre_topc(sK0,X1)) )
    | ~ spl1_4 ),
    inference(superposition,[],[f29,f54])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f80,plain,
    ( spl1_7
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f71,f67,f53,f43,f78])).

fof(f67,plain,
    ( spl1_5
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f71,plain,
    ( k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f61,f70])).

fof(f70,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f68,f54])).

fof(f68,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f61,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f56,f44])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_4 ),
    inference(superposition,[],[f36,f54])).

fof(f36,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
      | k2_struct_0(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_struct_0(X0) != X1
              | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ( k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              | k2_struct_0(X0) = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

fof(f75,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f70,f67,f53,f73])).

fof(f69,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f50,f43,f67])).

fof(f50,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_2 ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f55,plain,
    ( spl1_4
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f51,f43,f53])).

fof(f51,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f49,plain,(
    ~ spl1_3 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f47,plain,
    ( spl1_3
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f25,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(f45,plain,
    ( spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f41,f38,f43])).

fof(f41,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:15:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (9451)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (9453)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (9447)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (9457)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (9448)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (9461)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (9448)Refutation not found, incomplete strategy% (9448)------------------------------
% 0.22/0.50  % (9448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9448)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (9448)Memory used [KB]: 10490
% 0.22/0.50  % (9448)Time elapsed: 0.084 s
% 0.22/0.50  % (9448)------------------------------
% 0.22/0.50  % (9448)------------------------------
% 0.22/0.50  % (9447)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f40,f45,f49,f55,f69,f75,f80,f85,f93,f101,f118,f124,f134,f135])).
% 0.22/0.50  % (9455)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_struct_0(sK0)) != k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) != k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl1_14 | ~spl1_2 | ~spl1_4 | ~spl1_6 | ~spl1_8 | ~spl1_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f109,f99,f83,f73,f53,f43,f132])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    spl1_14 <=> k2_pre_topc(sK0,k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl1_2 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl1_4 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl1_6 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl1_8 <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl1_10 <=> m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) | (~spl1_2 | ~spl1_4 | ~spl1_6 | ~spl1_8 | ~spl1_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f108,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = k4_xboole_0(k2_struct_0(sK0),X0)) ) | ~spl1_6),
% 0.22/0.50    inference(resolution,[],[f74,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl1_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_struct_0(sK0)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | (~spl1_2 | ~spl1_4 | ~spl1_6 | ~spl1_8 | ~spl1_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f107,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | ~spl1_8),
% 0.22/0.50    inference(resolution,[],[f84,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.50  % (9454)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | ~spl1_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f83])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_struct_0(sK0)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))) | (~spl1_2 | ~spl1_4 | ~spl1_6 | ~spl1_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f102,f76])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    k2_pre_topc(sK0,k2_struct_0(sK0)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))) | (~spl1_2 | ~spl1_4 | ~spl1_10)),
% 0.22/0.50    inference(resolution,[],[f100,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3)) = X3) ) | (~spl1_2 | ~spl1_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f60,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl1_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f43])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3)) = X3) ) | ~spl1_4),
% 0.22/0.50    inference(superposition,[],[f26,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl1_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl1_12 | ~spl1_6 | ~spl1_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f119,f116,f73,f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl1_12 <=> k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl1_11 <=> k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) | (~spl1_6 | ~spl1_11)),
% 0.22/0.50    inference(superposition,[],[f117,f76])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | ~spl1_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl1_11 | ~spl1_2 | ~spl1_4 | ~spl1_6 | ~spl1_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f97,f91,f73,f53,f43,f116])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl1_9 <=> k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | (~spl1_2 | ~spl1_4 | ~spl1_6 | ~spl1_9)),
% 0.22/0.50    inference(forward_demodulation,[],[f96,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl1_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f91])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) | (~spl1_2 | ~spl1_4 | ~spl1_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f95,f76])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))) | (~spl1_2 | ~spl1_4 | ~spl1_6)),
% 0.22/0.50    inference(resolution,[],[f65,f74])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl1_10 | ~spl1_1 | ~spl1_4 | ~spl1_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f89,f73,f53,f38,f99])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    spl1_1 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl1_1 | ~spl1_4 | ~spl1_6)),
% 0.22/0.50    inference(resolution,[],[f64,f74])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl1_1 | ~spl1_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f59,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl1_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f38])).
% 0.22/0.50  % (9450)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl1_4),
% 0.22/0.50    inference(superposition,[],[f28,f54])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl1_9 | ~spl1_6 | ~spl1_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f86,f78,f73,f91])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl1_7 <=> k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl1_6 | ~spl1_7)),
% 0.22/0.50    inference(superposition,[],[f76,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl1_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl1_8 | ~spl1_1 | ~spl1_4 | ~spl1_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f81,f73,f53,f38,f83])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | (~spl1_1 | ~spl1_4 | ~spl1_6)),
% 0.22/0.50    inference(resolution,[],[f63,f74])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(X1,k2_pre_topc(sK0,X1))) ) | (~spl1_1 | ~spl1_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f58,f39])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(X1,k2_pre_topc(sK0,X1))) ) | ~spl1_4),
% 0.22/0.50    inference(superposition,[],[f29,f54])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl1_7 | ~spl1_2 | ~spl1_4 | ~spl1_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f71,f67,f53,f43,f78])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl1_5 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl1_2 | ~spl1_4 | ~spl1_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f61,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl1_4 | ~spl1_5)),
% 0.22/0.50    inference(forward_demodulation,[],[f68,f54])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl1_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl1_2 | ~spl1_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f56,f44])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | k1_xboole_0 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl1_4),
% 0.22/0.50    inference(superposition,[],[f36,f54])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) | k2_struct_0(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((k2_struct_0(X0) != X1 | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & (k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) | k2_struct_0(X0) = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl1_6 | ~spl1_4 | ~spl1_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f70,f67,f53,f73])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl1_5 | ~spl1_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f43,f67])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl1_2),
% 0.22/0.50    inference(resolution,[],[f44,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl1_4 | ~spl1_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f43,f53])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_2),
% 0.22/0.50    inference(resolution,[],[f44,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ~spl1_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl1_3 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl1_2 | ~spl1_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f38,f43])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl1_1),
% 0.22/0.50    inference(resolution,[],[f39,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    spl1_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f38])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (9447)------------------------------
% 0.22/0.50  % (9447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9447)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (9447)Memory used [KB]: 6140
% 0.22/0.50  % (9447)Time elapsed: 0.071 s
% 0.22/0.50  % (9447)------------------------------
% 0.22/0.50  % (9447)------------------------------
% 0.22/0.51  % (9446)Success in time 0.141 s
%------------------------------------------------------------------------------
