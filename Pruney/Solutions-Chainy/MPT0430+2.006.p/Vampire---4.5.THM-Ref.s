%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 108 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  176 ( 318 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f50,f58,f62,f66,f76,f92,f135,f157,f174])).

fof(f174,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f172,f29])).

fof(f29,plain,
    ( v3_setfam_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> v3_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f172,plain,
    ( ~ v3_setfam_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f168,f45])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v3_setfam_1(sK1,sK0)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(resolution,[],[f156,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ v3_setfam_1(X1,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ r2_hidden(X0,X1)
        | ~ v3_setfam_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f156,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_22
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f157,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f140,f133,f32,f155])).

fof(f32,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f133,plain,
    ( spl4_19
  <=> ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f140,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(resolution,[],[f134,f33])).

fof(f33,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f97,f90,f48,f133])).

fof(f48,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f90,plain,
    ( spl4_15
  <=> ! [X0] : r2_hidden(sK0,k2_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f97,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(superposition,[],[f91,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f91,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(sK2,X0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl4_15
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f79,f74,f56,f90])).

fof(f56,plain,
    ( spl4_8
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f74,plain,
    ( spl4_12
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f79,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(sK2,X0))
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f75,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl4_12
    | spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f72,f60,f40,f36,f74])).

fof(f36,plain,
    ( spl4_3
  <=> v3_setfam_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f40,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f60,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | r2_hidden(X0,X1)
        | v3_setfam_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f72,plain,
    ( r2_hidden(sK0,sK2)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f71,plain,
    ( r2_hidden(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( v3_setfam_1(X1,X0)
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f66,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f17,f64])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f62,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f16,f60])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f50,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f15,f48])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f46,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f14,f44])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ( r1_tarski(X2,X1)
                & v3_setfam_1(X1,X0) )
             => v3_setfam_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ( r1_tarski(X2,X1)
              & v3_setfam_1(X1,X0) )
           => v3_setfam_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

fof(f42,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f10,f40])).

fof(f10,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f13,f36])).

fof(f13,plain,(
    ~ v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f32])).

fof(f12,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (22021)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (22009)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (22002)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (22021)Refutation not found, incomplete strategy% (22021)------------------------------
% 0.20/0.48  % (22021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22021)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22021)Memory used [KB]: 10490
% 0.20/0.48  % (22021)Time elapsed: 0.061 s
% 0.20/0.48  % (22021)------------------------------
% 0.20/0.48  % (22021)------------------------------
% 0.20/0.49  % (22002)Refutation not found, incomplete strategy% (22002)------------------------------
% 0.20/0.49  % (22002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22010)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (22002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22002)Memory used [KB]: 10490
% 0.20/0.49  % (22002)Time elapsed: 0.057 s
% 0.20/0.49  % (22002)------------------------------
% 0.20/0.49  % (22002)------------------------------
% 0.20/0.50  % (22010)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f30,f34,f38,f42,f46,f50,f58,f62,f66,f76,f92,f135,f157,f174])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ~spl4_1 | ~spl4_5 | ~spl4_10 | ~spl4_22),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    $false | (~spl4_1 | ~spl4_5 | ~spl4_10 | ~spl4_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f172,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v3_setfam_1(sK1,sK0) | ~spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    spl4_1 <=> v3_setfam_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ~v3_setfam_1(sK1,sK0) | (~spl4_5 | ~spl4_10 | ~spl4_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f168,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl4_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~v3_setfam_1(sK1,sK0) | (~spl4_10 | ~spl4_22)),
% 0.20/0.50    inference(resolution,[],[f156,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v3_setfam_1(X1,X0)) ) | ~spl4_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl4_10 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    r2_hidden(sK0,sK1) | ~spl4_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl4_22 <=> r2_hidden(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    spl4_22 | ~spl4_2 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f140,f133,f32,f155])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    spl4_2 <=> r1_tarski(sK2,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    spl4_19 <=> ! [X0] : (r2_hidden(sK0,X0) | ~r1_tarski(sK2,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    r2_hidden(sK0,sK1) | (~spl4_2 | ~spl4_19)),
% 0.20/0.50    inference(resolution,[],[f134,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    r1_tarski(sK2,sK1) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f32])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(sK2,X0) | r2_hidden(sK0,X0)) ) | ~spl4_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f133])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl4_19 | ~spl4_6 | ~spl4_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f97,f90,f48,f133])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl4_6 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl4_15 <=> ! [X0] : r2_hidden(sK0,k2_xboole_0(sK2,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK0,X0) | ~r1_tarski(sK2,X0)) ) | (~spl4_6 | ~spl4_15)),
% 0.20/0.50    inference(superposition,[],[f91,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f48])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(sK2,X0))) ) | ~spl4_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f90])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    spl4_15 | ~spl4_8 | ~spl4_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f79,f74,f56,f90])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl4_8 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl4_12 <=> r2_hidden(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(sK2,X0))) ) | (~spl4_8 | ~spl4_12)),
% 0.20/0.50    inference(resolution,[],[f75,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) ) | ~spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f56])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    r2_hidden(sK0,sK2) | ~spl4_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl4_12 | spl4_3 | ~spl4_4 | ~spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f72,f60,f40,f36,f74])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    spl4_3 <=> v3_setfam_1(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl4_9 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    r2_hidden(sK0,sK2) | (spl4_3 | ~spl4_4 | ~spl4_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f40])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    r2_hidden(sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl4_3 | ~spl4_9)),
% 0.20/0.50    inference(resolution,[],[f61,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~v3_setfam_1(sK2,sK0) | spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f36])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v3_setfam_1(X1,X0) | r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f60])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl4_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f17,f64])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f16,f60])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f25,f56])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    spl4_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f15,f48])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f14,f44])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(flattening,[],[f6])).
% 0.20/0.50  fof(f6,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((~v3_setfam_1(X2,X0) & (r1_tarski(X2,X1) & v3_setfam_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f4])).
% 0.20/0.50  fof(f4,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f10,f40])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ~spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f13,f36])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ~v3_setfam_1(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f12,f32])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    r1_tarski(sK2,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f11,f28])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    v3_setfam_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (22010)------------------------------
% 0.20/0.50  % (22010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22010)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (22010)Memory used [KB]: 10618
% 0.20/0.50  % (22010)Time elapsed: 0.073 s
% 0.20/0.50  % (22010)------------------------------
% 0.20/0.50  % (22010)------------------------------
% 0.20/0.50  % (22000)Success in time 0.137 s
%------------------------------------------------------------------------------
