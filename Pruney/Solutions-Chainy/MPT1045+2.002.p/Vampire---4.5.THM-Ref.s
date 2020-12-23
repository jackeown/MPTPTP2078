%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:59 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 110 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  194 ( 338 expanded)
%              Number of equality atoms :   43 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f52,f57,f69,f74,f79,f85,f92,f94,f96,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f96,plain,
    ( ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f37,f56,f84,f64,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,X2) = k2_tarski(X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(definition_unfolding,[],[f30,f24])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(f64,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_6
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f84,plain,
    ( k2_tarski(sK2,sK2) != k5_partfun1(sK0,sK1,sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_10
  <=> k2_tarski(sK2,sK2) = k5_partfun1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f37,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f94,plain,
    ( spl3_4
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f51,f91,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f91,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f51,plain,
    ( k1_xboole_0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f92,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_1
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f60,f54,f89,f35,f40,f62])).

fof(f40,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f85,plain,
    ( ~ spl3_10
    | spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f80,f76,f71,f82])).

fof(f71,plain,
    ( spl3_8
  <=> k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( spl3_9
  <=> sK2 = k3_partfun1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( k2_tarski(sK2,sK2) != k5_partfun1(sK0,sK1,sK2)
    | spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f73,f78])).

fof(f78,plain,
    ( sK2 = k3_partfun1(sK2,sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f73,plain,
    ( k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k2_tarski(sK2,sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f79,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f58,f54,f35,f76])).

fof(f58,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k3_partfun1(sK2,sK0,sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f56,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

fof(f74,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

fof(f69,plain,
    ( spl3_6
    | ~ spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f59,f54,f66,f62])).

fof(f66,plain,
    ( spl3_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f59,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f19,f49,f45])).

fof(f45,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f19,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (14393)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (14386)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (14395)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (14395)Refutation not found, incomplete strategy% (14395)------------------------------
% 0.21/0.51  % (14395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14390)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (14403)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (14395)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14395)Memory used [KB]: 10746
% 0.21/0.52  % (14395)Time elapsed: 0.094 s
% 0.21/0.52  % (14395)------------------------------
% 0.21/0.52  % (14395)------------------------------
% 1.21/0.52  % (14411)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.21/0.52  % (14392)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.52  % (14407)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.52  % (14407)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.52  % SZS output start Proof for theBenchmark
% 1.21/0.52  fof(f98,plain,(
% 1.21/0.52    $false),
% 1.21/0.52    inference(avatar_sat_refutation,[],[f38,f43,f52,f57,f69,f74,f79,f85,f92,f94,f96,f97])).
% 1.21/0.52  fof(f97,plain,(
% 1.21/0.52    k1_xboole_0 != sK1 | k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(sK1)),
% 1.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.21/0.52  fof(f96,plain,(
% 1.21/0.52    ~spl3_1 | ~spl3_5 | ~spl3_6 | spl3_10),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f95])).
% 1.21/0.52  fof(f95,plain,(
% 1.21/0.52    $false | (~spl3_1 | ~spl3_5 | ~spl3_6 | spl3_10)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f37,f56,f84,f64,f32])).
% 1.21/0.52  fof(f32,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,X2) = k2_tarski(X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0)) )),
% 1.21/0.52    inference(definition_unfolding,[],[f30,f24])).
% 1.21/0.52  fof(f24,plain,(
% 1.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f2])).
% 1.21/0.52  fof(f2,axiom,(
% 1.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.21/0.52  fof(f30,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f18])).
% 1.21/0.52  fof(f18,plain,(
% 1.21/0.52    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.21/0.52    inference(flattening,[],[f17])).
% 1.21/0.52  fof(f17,plain,(
% 1.21/0.52    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.21/0.52    inference(ennf_transformation,[],[f5])).
% 1.21/0.52  fof(f5,axiom,(
% 1.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).
% 1.21/0.52  fof(f64,plain,(
% 1.21/0.52    v1_partfun1(sK2,sK0) | ~spl3_6),
% 1.21/0.52    inference(avatar_component_clause,[],[f62])).
% 1.21/0.52  fof(f62,plain,(
% 1.21/0.52    spl3_6 <=> v1_partfun1(sK2,sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.21/0.52  fof(f84,plain,(
% 1.21/0.52    k2_tarski(sK2,sK2) != k5_partfun1(sK0,sK1,sK2) | spl3_10),
% 1.21/0.52    inference(avatar_component_clause,[],[f82])).
% 1.21/0.52  fof(f82,plain,(
% 1.21/0.52    spl3_10 <=> k2_tarski(sK2,sK2) = k5_partfun1(sK0,sK1,sK2)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.21/0.52  fof(f56,plain,(
% 1.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 1.21/0.52    inference(avatar_component_clause,[],[f54])).
% 1.21/0.52  fof(f54,plain,(
% 1.21/0.52    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.21/0.52  fof(f37,plain,(
% 1.21/0.52    v1_funct_1(sK2) | ~spl3_1),
% 1.21/0.52    inference(avatar_component_clause,[],[f35])).
% 1.21/0.52  fof(f35,plain,(
% 1.21/0.52    spl3_1 <=> v1_funct_1(sK2)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.21/0.52  fof(f94,plain,(
% 1.21/0.52    spl3_4 | ~spl3_11),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f93])).
% 1.21/0.52  fof(f93,plain,(
% 1.21/0.52    $false | (spl3_4 | ~spl3_11)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f51,f91,f25])).
% 1.21/0.52  fof(f25,plain,(
% 1.21/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f11])).
% 1.21/0.52  fof(f11,plain,(
% 1.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f1])).
% 1.21/0.52  fof(f1,axiom,(
% 1.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.21/0.52  fof(f91,plain,(
% 1.21/0.52    v1_xboole_0(sK1) | ~spl3_11),
% 1.21/0.52    inference(avatar_component_clause,[],[f89])).
% 1.21/0.52  fof(f89,plain,(
% 1.21/0.52    spl3_11 <=> v1_xboole_0(sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.21/0.52  fof(f51,plain,(
% 1.21/0.52    k1_xboole_0 != sK1 | spl3_4),
% 1.21/0.52    inference(avatar_component_clause,[],[f49])).
% 1.21/0.52  fof(f49,plain,(
% 1.21/0.52    spl3_4 <=> k1_xboole_0 = sK1),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.21/0.52  fof(f92,plain,(
% 1.21/0.52    spl3_6 | ~spl3_2 | ~spl3_1 | spl3_11 | ~spl3_5),
% 1.21/0.52    inference(avatar_split_clause,[],[f60,f54,f89,f35,f40,f62])).
% 1.21/0.52  fof(f40,plain,(
% 1.21/0.52    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.21/0.52  fof(f60,plain,(
% 1.21/0.52    v1_xboole_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v1_partfun1(sK2,sK0) | ~spl3_5),
% 1.21/0.52    inference(resolution,[],[f56,f26])).
% 1.21/0.52  fof(f26,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f13])).
% 1.21/0.52  fof(f13,plain,(
% 1.21/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.21/0.52    inference(flattening,[],[f12])).
% 1.21/0.52  fof(f12,plain,(
% 1.21/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.21/0.52    inference(ennf_transformation,[],[f4])).
% 1.21/0.52  fof(f4,axiom,(
% 1.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.21/0.52  fof(f85,plain,(
% 1.21/0.52    ~spl3_10 | spl3_8 | ~spl3_9),
% 1.21/0.52    inference(avatar_split_clause,[],[f80,f76,f71,f82])).
% 1.21/0.52  fof(f71,plain,(
% 1.21/0.52    spl3_8 <=> k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) = k2_tarski(sK2,sK2)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.21/0.52  fof(f76,plain,(
% 1.21/0.52    spl3_9 <=> sK2 = k3_partfun1(sK2,sK0,sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.21/0.52  fof(f80,plain,(
% 1.21/0.52    k2_tarski(sK2,sK2) != k5_partfun1(sK0,sK1,sK2) | (spl3_8 | ~spl3_9)),
% 1.21/0.52    inference(forward_demodulation,[],[f73,f78])).
% 1.21/0.52  fof(f78,plain,(
% 1.21/0.52    sK2 = k3_partfun1(sK2,sK0,sK1) | ~spl3_9),
% 1.21/0.52    inference(avatar_component_clause,[],[f76])).
% 1.21/0.52  fof(f73,plain,(
% 1.21/0.52    k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k2_tarski(sK2,sK2) | spl3_8),
% 1.21/0.52    inference(avatar_component_clause,[],[f71])).
% 1.21/0.52  fof(f79,plain,(
% 1.21/0.52    spl3_9 | ~spl3_1 | ~spl3_5),
% 1.21/0.52    inference(avatar_split_clause,[],[f58,f54,f35,f76])).
% 1.21/0.52  fof(f58,plain,(
% 1.21/0.52    ~v1_funct_1(sK2) | sK2 = k3_partfun1(sK2,sK0,sK1) | ~spl3_5),
% 1.21/0.52    inference(resolution,[],[f56,f28])).
% 1.21/0.52  fof(f28,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k3_partfun1(X2,X0,X1) = X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f16])).
% 1.21/0.52  fof(f16,plain,(
% 1.21/0.52    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.21/0.52    inference(flattening,[],[f15])).
% 1.21/0.52  fof(f15,plain,(
% 1.21/0.52    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.21/0.52    inference(ennf_transformation,[],[f6])).
% 1.21/0.52  fof(f6,axiom,(
% 1.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).
% 1.21/0.52  fof(f74,plain,(
% 1.21/0.52    ~spl3_8),
% 1.21/0.52    inference(avatar_split_clause,[],[f31,f71])).
% 1.21/0.52  fof(f31,plain,(
% 1.21/0.52    k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k2_tarski(sK2,sK2)),
% 1.21/0.52    inference(definition_unfolding,[],[f23,f24])).
% 1.21/0.52  fof(f23,plain,(
% 1.21/0.52    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))),
% 1.21/0.52    inference(cnf_transformation,[],[f10])).
% 1.21/0.52  fof(f10,plain,(
% 1.21/0.52    ? [X0,X1,X2] : (k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.21/0.52    inference(flattening,[],[f9])).
% 1.21/0.52  fof(f9,plain,(
% 1.21/0.52    ? [X0,X1,X2] : ((k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.21/0.52    inference(ennf_transformation,[],[f8])).
% 1.21/0.52  fof(f8,negated_conjecture,(
% 1.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 1.21/0.52    inference(negated_conjecture,[],[f7])).
% 1.21/0.52  fof(f7,conjecture,(
% 1.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).
% 1.21/0.52  fof(f69,plain,(
% 1.21/0.52    spl3_6 | ~spl3_7 | ~spl3_5),
% 1.21/0.52    inference(avatar_split_clause,[],[f59,f54,f66,f62])).
% 1.21/0.52  fof(f66,plain,(
% 1.21/0.52    spl3_7 <=> v1_xboole_0(sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.21/0.52  fof(f59,plain,(
% 1.21/0.52    ~v1_xboole_0(sK0) | v1_partfun1(sK2,sK0) | ~spl3_5),
% 1.21/0.52    inference(resolution,[],[f56,f27])).
% 1.21/0.52  fof(f27,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f14])).
% 1.21/0.52  fof(f14,plain,(
% 1.21/0.52    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f3])).
% 1.21/0.52  fof(f3,axiom,(
% 1.21/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 1.21/0.52  fof(f57,plain,(
% 1.21/0.52    spl3_5),
% 1.21/0.52    inference(avatar_split_clause,[],[f22,f54])).
% 1.21/0.52  fof(f22,plain,(
% 1.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.21/0.52    inference(cnf_transformation,[],[f10])).
% 1.21/0.52  fof(f52,plain,(
% 1.21/0.52    spl3_3 | ~spl3_4),
% 1.21/0.52    inference(avatar_split_clause,[],[f19,f49,f45])).
% 1.21/0.52  fof(f45,plain,(
% 1.21/0.52    spl3_3 <=> k1_xboole_0 = sK0),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.21/0.52  fof(f19,plain,(
% 1.21/0.52    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.21/0.52    inference(cnf_transformation,[],[f10])).
% 1.21/0.52  fof(f43,plain,(
% 1.21/0.52    spl3_2),
% 1.21/0.52    inference(avatar_split_clause,[],[f21,f40])).
% 1.21/0.52  fof(f21,plain,(
% 1.21/0.52    v1_funct_2(sK2,sK0,sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f10])).
% 1.21/0.52  fof(f38,plain,(
% 1.21/0.52    spl3_1),
% 1.21/0.52    inference(avatar_split_clause,[],[f20,f35])).
% 1.21/0.52  fof(f20,plain,(
% 1.21/0.52    v1_funct_1(sK2)),
% 1.21/0.52    inference(cnf_transformation,[],[f10])).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (14407)------------------------------
% 1.21/0.52  % (14407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (14407)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (14407)Memory used [KB]: 10746
% 1.21/0.52  % (14407)Time elapsed: 0.075 s
% 1.21/0.52  % (14407)------------------------------
% 1.21/0.52  % (14407)------------------------------
% 1.21/0.52  % (14384)Success in time 0.162 s
%------------------------------------------------------------------------------
