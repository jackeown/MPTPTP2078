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
% DateTime   : Thu Dec  3 13:03:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   54 (  89 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 205 expanded)
%              Number of equality atoms :   47 (  86 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f42,f49,f55,f73])).

fof(f73,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f54,f71])).

fof(f71,plain,
    ( ! [X0,X1] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f68,f48])).

fof(f48,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f68,plain,
    ( ! [X0,X1] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1)
    | ~ spl3_3 ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X4,X5,X6) ) ),
    inference(forward_demodulation,[],[f64,f29])).

fof(f29,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X4,X5,X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) ) ),
    inference(superposition,[],[f63,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X1,X2,X0,X3) = k3_xboole_0(k8_relset_1(X1,X2,X0,X3),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f27,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f54,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_5
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f55,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f50,f47,f31,f53])).

fof(f31,plain,
    ( spl3_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f32,f48])).

fof(f32,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f49,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f40,f47])).

fof(f45,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f44,f21])).

fof(f44,plain,
    ( sK2 = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_3 ),
    inference(resolution,[],[f43,f41])).

fof(f42,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f38,f35,f40])).

fof(f35,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f36,f29])).

fof(f36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f31])).

fof(f20,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.23/0.48  % (29995)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.23/0.48  % (30001)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.23/0.50  % (29986)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.50  % (29986)Refutation not found, incomplete strategy% (29986)------------------------------
% 0.23/0.50  % (29986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (29997)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (29986)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (29986)Memory used [KB]: 10490
% 0.23/0.51  % (29986)Time elapsed: 0.067 s
% 0.23/0.51  % (29986)------------------------------
% 0.23/0.51  % (29986)------------------------------
% 0.23/0.51  % (29993)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.51  % (29988)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.51  % (29990)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.52  % (29988)Refutation not found, incomplete strategy% (29988)------------------------------
% 0.23/0.52  % (29988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (29988)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (29988)Memory used [KB]: 10618
% 0.23/0.52  % (29988)Time elapsed: 0.074 s
% 0.23/0.52  % (29988)------------------------------
% 0.23/0.52  % (29988)------------------------------
% 0.23/0.52  % (29987)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.52  % (29989)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.52  % (30002)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.52  % (29991)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.52  % (30004)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.23/0.53  % (29991)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f75,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(avatar_sat_refutation,[],[f33,f37,f42,f49,f55,f73])).
% 0.23/0.53  fof(f73,plain,(
% 0.23/0.53    ~spl3_3 | ~spl3_4 | spl3_5),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f72])).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    $false | (~spl3_3 | ~spl3_4 | spl3_5)),
% 0.23/0.53    inference(subsumption_resolution,[],[f54,f71])).
% 0.23/0.53  fof(f71,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)) ) | (~spl3_3 | ~spl3_4)),
% 0.23/0.53    inference(forward_demodulation,[],[f68,f48])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    k1_xboole_0 = sK2 | ~spl3_4),
% 0.23/0.53    inference(avatar_component_clause,[],[f47])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    spl3_4 <=> k1_xboole_0 = sK2),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1)) ) | ~spl3_3),
% 0.23/0.53    inference(resolution,[],[f66,f41])).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_3),
% 0.23/0.53    inference(avatar_component_clause,[],[f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    ( ! [X6,X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X4,X5,X6)) )),
% 0.23/0.53    inference(forward_demodulation,[],[f64,f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.23/0.53    inference(equality_resolution,[],[f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.53    inference(flattening,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.53    inference(nnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.53  fof(f64,plain,(
% 0.23/0.53    ( ! [X6,X4,X5] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X4,X5,X6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))) )),
% 0.23/0.53    inference(superposition,[],[f63,f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X1,X2,X0,X3) = k3_xboole_0(k8_relset_1(X1,X2,X0,X3),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.23/0.53    inference(resolution,[],[f27,f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.53    inference(resolution,[],[f22,f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.23/0.53    inference(ennf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,plain,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.23/0.53    inference(unused_predicate_definition_removal,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.53    inference(ennf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl3_5),
% 0.23/0.53    inference(avatar_component_clause,[],[f53])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    spl3_5 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ~spl3_5 | spl3_1 | ~spl3_4),
% 0.23/0.53    inference(avatar_split_clause,[],[f50,f47,f31,f53])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    spl3_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl3_1 | ~spl3_4)),
% 0.23/0.53    inference(superposition,[],[f32,f48])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f31])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    spl3_4 | ~spl3_3),
% 0.23/0.53    inference(avatar_split_clause,[],[f45,f40,f47])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    k1_xboole_0 = sK2 | ~spl3_3),
% 0.23/0.53    inference(forward_demodulation,[],[f44,f21])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    sK2 = k3_xboole_0(sK2,k1_xboole_0) | ~spl3_3),
% 0.23/0.53    inference(resolution,[],[f43,f41])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    spl3_3 | ~spl3_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f38,f35,f40])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_2),
% 0.23/0.53    inference(forward_demodulation,[],[f36,f29])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f35])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    spl3_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f19,f35])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.23/0.53    inference(ennf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.53    inference(pure_predicate_removal,[],[f9])).
% 0.23/0.53  fof(f9,plain,(
% 0.23/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.53    inference(pure_predicate_removal,[],[f7])).
% 0.23/0.53  fof(f7,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.53    inference(negated_conjecture,[],[f6])).
% 0.23/0.53  fof(f6,conjecture,(
% 0.23/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ~spl3_1),
% 0.23/0.53    inference(avatar_split_clause,[],[f20,f31])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (29991)------------------------------
% 0.23/0.53  % (29991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (29991)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (29991)Memory used [KB]: 10618
% 0.23/0.53  % (29991)Time elapsed: 0.101 s
% 0.23/0.53  % (29991)------------------------------
% 0.23/0.53  % (29991)------------------------------
% 0.23/0.53  % (29994)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.53  % (29992)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.53  % (29998)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.53  % (29998)Refutation not found, incomplete strategy% (29998)------------------------------
% 0.23/0.53  % (29998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (29998)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (29998)Memory used [KB]: 1535
% 0.23/0.53  % (29998)Time elapsed: 0.071 s
% 0.23/0.53  % (29998)------------------------------
% 0.23/0.53  % (29998)------------------------------
% 0.23/0.53  % (30003)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.23/0.53  % (29996)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.53  % (30000)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.53  % (29979)Success in time 0.158 s
%------------------------------------------------------------------------------
