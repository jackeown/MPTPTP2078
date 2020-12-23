%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 (  97 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 186 expanded)
%              Number of equality atoms :   52 (  73 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f61,f73,f77,f85,f89,f109,f125,f129,f176,f192,f211,f215])).

fof(f215,plain,
    ( ~ spl1_9
    | ~ spl1_14
    | spl1_22
    | ~ spl1_28 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl1_9
    | ~ spl1_14
    | spl1_22
    | ~ spl1_28 ),
    inference(subsumption_resolution,[],[f175,f213])).

fof(f213,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_9
    | ~ spl1_14
    | ~ spl1_28 ),
    inference(forward_demodulation,[],[f212,f88])).

fof(f88,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl1_9
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f212,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)
    | ~ spl1_14
    | ~ spl1_28 ),
    inference(superposition,[],[f108,f210])).

fof(f210,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl1_28 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl1_28
  <=> ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f108,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl1_14
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f175,plain,
    ( sK0 != k4_xboole_0(sK0,k1_xboole_0)
    | spl1_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl1_22
  <=> sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f211,plain,
    ( spl1_28
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f146,f123,f87,f83,f75,f209])).

fof(f75,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f83,plain,
    ( spl1_8
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f123,plain,
    ( spl1_17
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f146,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f145,f76])).

fof(f76,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f145,plain,
    ( ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,X1)
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f139,f84])).

fof(f84,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f139,plain,
    ( ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(superposition,[],[f124,f88])).

fof(f124,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f192,plain,
    ( ~ spl1_5
    | spl1_21 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl1_5
    | spl1_21 ),
    inference(unit_resulting_resolution,[],[f72,f171])).

fof(f171,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl1_21 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl1_21
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f72,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_5
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f176,plain,
    ( ~ spl1_21
    | ~ spl1_22
    | spl1_2
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f150,f127,f58,f173,f169])).

fof(f58,plain,
    ( spl1_2
  <=> sK0 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f127,plain,
    ( spl1_18
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f150,plain,
    ( sK0 != k4_xboole_0(sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl1_2
    | ~ spl1_18 ),
    inference(superposition,[],[f60,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f60,plain,
    ( sK0 != k3_subset_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f129,plain,(
    spl1_18 ),
    inference(avatar_split_clause,[],[f42,f127])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f125,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f41,f123])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f109,plain,(
    spl1_14 ),
    inference(avatar_split_clause,[],[f40,f107])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f89,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f34,f87])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f85,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f33,f83])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f77,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f73,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f50,f71])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f61,plain,
    ( ~ spl1_2
    | spl1_1 ),
    inference(avatar_split_clause,[],[f56,f52,f58])).

fof(f52,plain,
    ( spl1_1
  <=> k2_subset_1(sK0) = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f56,plain,
    ( sK0 != k3_subset_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(forward_demodulation,[],[f54,f30])).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,
    ( k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f49,f52])).

fof(f49,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f28,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).

fof(f26,plain,
    ( ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))
   => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:28:59 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.45  % (29321)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (29321)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f216,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f55,f61,f73,f77,f85,f89,f109,f125,f129,f176,f192,f211,f215])).
% 0.22/0.46  fof(f215,plain,(
% 0.22/0.46    ~spl1_9 | ~spl1_14 | spl1_22 | ~spl1_28),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f214])).
% 0.22/0.46  fof(f214,plain,(
% 0.22/0.46    $false | (~spl1_9 | ~spl1_14 | spl1_22 | ~spl1_28)),
% 0.22/0.46    inference(subsumption_resolution,[],[f175,f213])).
% 0.22/0.46  fof(f213,plain,(
% 0.22/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl1_9 | ~spl1_14 | ~spl1_28)),
% 0.22/0.46    inference(forward_demodulation,[],[f212,f88])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f87])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    spl1_9 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.46  fof(f212,plain,(
% 0.22/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) ) | (~spl1_14 | ~spl1_28)),
% 0.22/0.46    inference(superposition,[],[f108,f210])).
% 0.22/0.46  fof(f210,plain,(
% 0.22/0.46    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl1_28),
% 0.22/0.46    inference(avatar_component_clause,[],[f209])).
% 0.22/0.46  fof(f209,plain,(
% 0.22/0.46    spl1_28 <=> ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl1_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f107])).
% 0.22/0.46  fof(f107,plain,(
% 0.22/0.46    spl1_14 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.46  fof(f175,plain,(
% 0.22/0.46    sK0 != k4_xboole_0(sK0,k1_xboole_0) | spl1_22),
% 0.22/0.46    inference(avatar_component_clause,[],[f173])).
% 0.22/0.46  fof(f173,plain,(
% 0.22/0.46    spl1_22 <=> sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.22/0.46  fof(f211,plain,(
% 0.22/0.46    spl1_28 | ~spl1_6 | ~spl1_8 | ~spl1_9 | ~spl1_17),
% 0.22/0.46    inference(avatar_split_clause,[],[f146,f123,f87,f83,f75,f209])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    spl1_6 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    spl1_8 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.46  fof(f123,plain,(
% 0.22/0.46    spl1_17 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.22/0.46  fof(f146,plain,(
% 0.22/0.46    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | (~spl1_6 | ~spl1_8 | ~spl1_9 | ~spl1_17)),
% 0.22/0.46    inference(forward_demodulation,[],[f145,f76])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl1_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f75])).
% 0.22/0.46  fof(f145,plain,(
% 0.22/0.46    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,X1)) ) | (~spl1_8 | ~spl1_9 | ~spl1_17)),
% 0.22/0.46    inference(forward_demodulation,[],[f139,f84])).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f83])).
% 0.22/0.46  fof(f139,plain,(
% 0.22/0.46    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))) ) | (~spl1_9 | ~spl1_17)),
% 0.22/0.46    inference(superposition,[],[f124,f88])).
% 0.22/0.46  fof(f124,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | ~spl1_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f123])).
% 0.22/0.46  fof(f192,plain,(
% 0.22/0.46    ~spl1_5 | spl1_21),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f189])).
% 0.22/0.46  fof(f189,plain,(
% 0.22/0.46    $false | (~spl1_5 | spl1_21)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f72,f171])).
% 0.22/0.46  fof(f171,plain,(
% 0.22/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | spl1_21),
% 0.22/0.46    inference(avatar_component_clause,[],[f169])).
% 0.22/0.46  fof(f169,plain,(
% 0.22/0.46    spl1_21 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl1_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f71])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    spl1_5 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.46  fof(f176,plain,(
% 0.22/0.46    ~spl1_21 | ~spl1_22 | spl1_2 | ~spl1_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f150,f127,f58,f173,f169])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    spl1_2 <=> sK0 = k3_subset_1(sK0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    spl1_18 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.22/0.46  fof(f150,plain,(
% 0.22/0.46    sK0 != k4_xboole_0(sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | (spl1_2 | ~spl1_18)),
% 0.22/0.46    inference(superposition,[],[f60,f128])).
% 0.22/0.46  fof(f128,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl1_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f127])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    sK0 != k3_subset_1(sK0,k1_xboole_0) | spl1_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f58])).
% 0.22/0.46  fof(f129,plain,(
% 0.22/0.46    spl1_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f42,f127])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.46  fof(f125,plain,(
% 0.22/0.46    spl1_17),
% 0.22/0.46    inference(avatar_split_clause,[],[f41,f123])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.46  fof(f109,plain,(
% 0.22/0.46    spl1_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f40,f107])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    spl1_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f34,f87])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    spl1_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f33,f83])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    spl1_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f31,f75])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    spl1_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f50,f71])).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f35,f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,axiom,(
% 0.22/0.46    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,axiom,(
% 0.22/0.46    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ~spl1_2 | spl1_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f56,f52,f58])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    spl1_1 <=> k2_subset_1(sK0) = k3_subset_1(sK0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    sK0 != k3_subset_1(sK0,k1_xboole_0) | spl1_1),
% 0.22/0.46    inference(forward_demodulation,[],[f54,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,axiom,(
% 0.22/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0) | spl1_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f52])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    ~spl1_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f49,f52])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0)),
% 0.22/0.46    inference(forward_demodulation,[],[f28,f29])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f22])).
% 0.22/0.46  fof(f22,negated_conjecture,(
% 0.22/0.46    ~! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.46    inference(negated_conjecture,[],[f21])).
% 0.22/0.46  fof(f21,conjecture,(
% 0.22/0.46    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (29321)------------------------------
% 0.22/0.46  % (29321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (29321)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (29321)Memory used [KB]: 6140
% 0.22/0.46  % (29321)Time elapsed: 0.013 s
% 0.22/0.46  % (29321)------------------------------
% 0.22/0.46  % (29321)------------------------------
% 0.22/0.47  % (29310)Success in time 0.093 s
%------------------------------------------------------------------------------
