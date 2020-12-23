%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 107 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :  127 ( 197 expanded)
%              Number of equality atoms :   51 (  85 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f42,f49,f58,f80,f100,f106,f112,f288,f307,f328,f341])).

fof(f341,plain,
    ( sK2 != k3_xboole_0(sK1,sK2)
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f328,plain,
    ( spl3_36
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f317,f297,f324])).

fof(f324,plain,
    ( spl3_36
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f297,plain,
    ( spl3_33
  <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f317,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_33 ),
    inference(superposition,[],[f21,f299])).

fof(f299,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f297])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f307,plain,
    ( spl3_33
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f292,f285,f297])).

fof(f285,plain,
    ( spl3_32
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f292,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_32 ),
    inference(superposition,[],[f26,f287])).

fof(f287,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f285])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f288,plain,
    ( spl3_32
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f283,f109,f103,f285])).

fof(f103,plain,
    ( spl3_11
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f109,plain,
    ( spl3_12
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f283,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f111,f105])).

fof(f105,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f111,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f112,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f107,f97,f109])).

fof(f97,plain,
    ( spl3_10
  <=> r1_tarski(k4_xboole_0(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f107,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))
    | ~ spl3_10 ),
    inference(resolution,[],[f99,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f99,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f106,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f101,f77,f103])).

fof(f77,plain,
    ( spl3_8
  <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f101,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f87,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

% (26116)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (26104)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (26117)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (26105)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (26120)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (26112)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f87,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f21,f79])).

fof(f79,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f100,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f86,f77,f97])).

fof(f86,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f18,f79])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f80,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f67,f54,f77])).

fof(f54,plain,
    ( spl3_5
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f67,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f23,f56])).

fof(f56,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f58,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f51,f39,f54])).

fof(f39,plain,
    ( spl3_3
  <=> sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f22,f41])).

fof(f41,plain,
    ( sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f49,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f44,f28,f46])).

fof(f46,plain,
    ( spl3_4
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f28,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f43,f21])).

fof(f43,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(superposition,[],[f30,f26])).

fof(f30,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f42,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f33,f39])).

fof(f33,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f24])).

fof(f35,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

% (26113)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (26103)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.43  % (26118)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (26108)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (26107)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (26106)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (26119)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (26114)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (26109)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (26115)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (26114)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f342,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f31,f36,f42,f49,f58,f80,f100,f106,f112,f288,f307,f328,f341])).
% 0.20/0.48  fof(f341,plain,(
% 0.20/0.48    sK2 != k3_xboole_0(sK1,sK2) | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f328,plain,(
% 0.20/0.48    spl3_36 | ~spl3_33),
% 0.20/0.48    inference(avatar_split_clause,[],[f317,f297,f324])).
% 0.20/0.48  fof(f324,plain,(
% 0.20/0.48    spl3_36 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.48  fof(f297,plain,(
% 0.20/0.48    spl3_33 <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.48  fof(f317,plain,(
% 0.20/0.48    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_33),
% 0.20/0.48    inference(superposition,[],[f21,f299])).
% 0.20/0.48  fof(f299,plain,(
% 0.20/0.48    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_33),
% 0.20/0.48    inference(avatar_component_clause,[],[f297])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.48  fof(f307,plain,(
% 0.20/0.48    spl3_33 | ~spl3_32),
% 0.20/0.48    inference(avatar_split_clause,[],[f292,f285,f297])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    spl3_32 <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.48  fof(f292,plain,(
% 0.20/0.48    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_32),
% 0.20/0.48    inference(superposition,[],[f26,f287])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) | ~spl3_32),
% 0.20/0.48    inference(avatar_component_clause,[],[f285])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.48  fof(f288,plain,(
% 0.20/0.48    spl3_32 | ~spl3_11 | ~spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f283,f109,f103,f285])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl3_11 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl3_12 <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_12)),
% 0.20/0.48    inference(forward_demodulation,[],[f111,f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | ~spl3_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f103])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f109])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl3_12 | ~spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f107,f97,f109])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl3_10 <=> r1_tarski(k4_xboole_0(sK1,sK1),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) | ~spl3_10),
% 0.20/0.48    inference(resolution,[],[f99,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    r1_tarski(k4_xboole_0(sK1,sK1),sK2) | ~spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_11 | ~spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f101,f77,f103])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl3_8 <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | ~spl3_8),
% 0.20/0.48    inference(forward_demodulation,[],[f87,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  % (26116)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (26104)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (26117)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (26105)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (26120)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (26112)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | ~spl3_8),
% 0.20/0.50    inference(superposition,[],[f21,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl3_10 | ~spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f86,f77,f97])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    r1_tarski(k4_xboole_0(sK1,sK1),sK2) | ~spl3_8),
% 0.20/0.50    inference(superposition,[],[f18,f79])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl3_8 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f67,f54,f77])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl3_5 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_5),
% 0.20/0.50    inference(superposition,[],[f23,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f54])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl3_5 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f51,f39,f54])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    spl3_3 <=> sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_3),
% 0.20/0.50    inference(superposition,[],[f22,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f39])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ~spl3_4 | spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f44,f28,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    spl3_4 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    spl3_1 <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_1),
% 0.20/0.50    inference(forward_demodulation,[],[f43,f21])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_1),
% 0.20/0.50    inference(superposition,[],[f30,f26])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f28])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl3_3 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f33,f39])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f35,f24])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f33])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f16,f33])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    r1_tarski(sK2,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  % (26113)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f17,f28])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (26114)------------------------------
% 0.20/0.50  % (26114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26114)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (26114)Memory used [KB]: 10746
% 0.20/0.50  % (26114)Time elapsed: 0.072 s
% 0.20/0.50  % (26114)------------------------------
% 0.20/0.50  % (26114)------------------------------
% 0.20/0.50  % (26095)Success in time 0.144 s
%------------------------------------------------------------------------------
