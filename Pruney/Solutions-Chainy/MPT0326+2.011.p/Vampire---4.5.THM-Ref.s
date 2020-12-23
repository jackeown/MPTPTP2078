%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 134 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :    5
%              Number of atoms          :  227 ( 365 expanded)
%              Number of equality atoms :   56 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f43,f47,f63,f74,f82,f86,f90,f99,f107,f122,f132,f152,f166,f176,f195])).

fof(f195,plain,
    ( spl4_24
    | spl4_23
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f192,f120,f72,f147,f150])).

fof(f150,plain,
    ( spl4_24
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f147,plain,
    ( spl4_23
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f72,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f120,plain,
    ( spl4_19
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(superposition,[],[f73,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f72])).

fof(f176,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f172,f35])).

fof(f35,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f172,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_1
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f27,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f150])).

fof(f27,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f166,plain,
    ( spl4_2
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl4_2
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f153,f85])).

fof(f85,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_14
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f153,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl4_2
    | ~ spl4_23 ),
    inference(backward_demodulation,[],[f31,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f152,plain,
    ( spl4_23
    | spl4_24
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f139,f130,f72,f150,f147])).

fof(f130,plain,
    ( spl4_20
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f139,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(superposition,[],[f73,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f123,f97,f38,f130])).

fof(f38,plain,
    ( spl4_4
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f97,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k2_zfmisc_1(sK1,X0)
        | ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f123,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(resolution,[],[f39,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1))
        | k1_xboole_0 = k2_zfmisc_1(sK1,X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f97])).

fof(f39,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f122,plain,
    ( spl4_19
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f112,f105,f41,f120])).

fof(f41,plain,
    ( spl4_5
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f105,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,sK1)
        | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f112,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
        | k1_xboole_0 = k2_zfmisc_1(X0,sK1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f105])).

% (29669)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f107,plain,
    ( spl4_17
    | spl4_2
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f94,f88,f30,f105])).

fof(f88,plain,
    ( spl4_15
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | r1_tarski(X1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,sK1)
        | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) )
    | spl4_2
    | ~ spl4_15 ),
    inference(resolution,[],[f89,f31])).

fof(f89,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(X1,X3)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f88])).

fof(f99,plain,
    ( spl4_16
    | spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f91,f80,f30,f97])).

fof(f80,plain,
    ( spl4_13
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(sK1,X0)
        | ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) )
    | spl4_2
    | ~ spl4_13 ),
    inference(resolution,[],[f81,f31])).

fof(f81,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(X0,X2)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f80])).

fof(f90,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f22,f88])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f86,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f66,f61,f45,f84])).

fof(f45,plain,
    ( spl4_6
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(superposition,[],[f62,f46])).

fof(f46,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f61])).

fof(f82,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f21,f80])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f18,f72])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f63,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f17,f61])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f47,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f15,f45])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f43,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f11,f41,f38])).

fof(f11,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f14,f34])).

fof(f14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f32,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f13,f26])).

fof(f13,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (29680)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % (29672)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (29668)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (29677)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (29672)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f28,f32,f36,f43,f47,f63,f74,f82,f86,f90,f99,f107,f122,f132,f152,f166,f176,f195])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    spl4_24 | spl4_23 | ~spl4_12 | ~spl4_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f192,f120,f72,f147,f150])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    spl4_24 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl4_23 <=> k1_xboole_0 = sK1),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl4_12 <=> ! [X1,X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl4_19 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl4_12 | ~spl4_19)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f191])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl4_12 | ~spl4_19)),
% 0.22/0.48    inference(superposition,[],[f73,f121])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f120])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl4_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f72])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    spl4_1 | ~spl4_3 | ~spl4_24),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    $false | (spl4_1 | ~spl4_3 | ~spl4_24)),
% 0.22/0.48    inference(subsumption_resolution,[],[f172,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | (spl4_1 | ~spl4_24)),
% 0.22/0.48    inference(backward_demodulation,[],[f27,f151])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl4_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f150])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0) | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    spl4_1 <=> v1_xboole_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    spl4_2 | ~spl4_14 | ~spl4_23),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    $false | (spl4_2 | ~spl4_14 | ~spl4_23)),
% 0.22/0.48    inference(subsumption_resolution,[],[f153,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl4_14 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ~r1_tarski(k1_xboole_0,sK3) | (spl4_2 | ~spl4_23)),
% 0.22/0.48    inference(backward_demodulation,[],[f31,f148])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | ~spl4_23),
% 0.22/0.48    inference(avatar_component_clause,[],[f147])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK3) | spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    spl4_2 <=> r1_tarski(sK1,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    spl4_23 | spl4_24 | ~spl4_12 | ~spl4_20),
% 0.22/0.48    inference(avatar_split_clause,[],[f139,f130,f72,f150,f147])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    spl4_20 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl4_12 | ~spl4_20)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl4_12 | ~spl4_20)),
% 0.22/0.48    inference(superposition,[],[f73,f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl4_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f130])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl4_20 | ~spl4_4 | ~spl4_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f123,f97,f38,f130])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl4_4 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl4_16 <=> ! [X1,X0] : (k1_xboole_0 = k2_zfmisc_1(sK1,X0) | ~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | (~spl4_4 | ~spl4_16)),
% 0.22/0.48    inference(resolution,[],[f39,f98])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) | k1_xboole_0 = k2_zfmisc_1(sK1,X0)) ) | ~spl4_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f97])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f38])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl4_19 | ~spl4_5 | ~spl4_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f112,f105,f41,f120])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl4_5 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl4_17 <=> ! [X1,X0] : (k1_xboole_0 = k2_zfmisc_1(X0,sK1) | ~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl4_5 | ~spl4_17)),
% 0.22/0.48    inference(resolution,[],[f106,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) | k1_xboole_0 = k2_zfmisc_1(X0,sK1)) ) | ~spl4_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  % (29669)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl4_17 | spl4_2 | ~spl4_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f94,f88,f30,f105])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl4_15 <=> ! [X1,X3,X0,X2] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,sK1) | ~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) ) | (spl4_2 | ~spl4_15)),
% 0.22/0.48    inference(resolution,[],[f89,f31])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | ~spl4_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl4_16 | spl4_2 | ~spl4_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f91,f80,f30,f97])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl4_13 <=> ! [X1,X3,X0,X2] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(sK1,X0) | ~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1))) ) | (spl4_2 | ~spl4_13)),
% 0.22/0.48    inference(resolution,[],[f81,f31])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | ~spl4_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f80])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl4_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f88])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl4_14 | ~spl4_6 | ~spl4_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f66,f61,f45,f84])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl4_6 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl4_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl4_6 | ~spl4_10)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) ) | (~spl4_6 | ~spl4_10)),
% 0.22/0.48    inference(superposition,[],[f62,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) ) | ~spl4_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl4_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f80])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl4_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f72])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl4_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f61])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f15,f45])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl4_4 | spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f11,f41,f38])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f14,f34])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f12,f30])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ~spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f13,f26])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (29672)------------------------------
% 0.22/0.48  % (29672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29672)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (29672)Memory used [KB]: 10618
% 0.22/0.48  % (29672)Time elapsed: 0.062 s
% 0.22/0.48  % (29672)------------------------------
% 0.22/0.48  % (29672)------------------------------
% 0.22/0.48  % (29662)Success in time 0.115 s
%------------------------------------------------------------------------------
