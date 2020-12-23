%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 126 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  178 ( 460 expanded)
%              Number of equality atoms :  106 ( 355 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f661,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f104,f111,f616,f622,f627,f660])).

fof(f660,plain,
    ( ~ spl9_1
    | ~ spl9_4
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_4
    | spl9_5 ),
    inference(subsumption_resolution,[],[f658,f110])).

fof(f110,plain,
    ( sK4 != sK5
    | spl9_5 ),
    inference(avatar_component_clause,[],[f108])).

% (11579)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f108,plain,
    ( spl9_5
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f658,plain,
    ( sK4 = sK5
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f102,f89])).

fof(f89,plain,
    ( sK4 = k1_tarski(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl9_1
  <=> sK4 = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f102,plain,
    ( sK5 = k1_tarski(sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_4
  <=> sK5 = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f627,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f626,f92,f101])).

fof(f92,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f626,plain,
    ( sK5 = k1_tarski(sK3)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f624,f94])).

% (11570)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f94,plain,
    ( k1_xboole_0 != sK5
    | spl9_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f624,plain,
    ( k1_xboole_0 = sK5
    | sK5 = k1_tarski(sK3) ),
    inference(resolution,[],[f176,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f176,plain,(
    r1_tarski(sK5,k1_tarski(sK3)) ),
    inference(superposition,[],[f172,f46])).

fof(f46,plain,(
    k1_tarski(sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 != sK5
      | sK4 != k1_tarski(sK3) )
    & ( sK5 != k1_tarski(sK3)
      | k1_xboole_0 != sK4 )
    & ( sK5 != k1_tarski(sK3)
      | sK4 != k1_tarski(sK3) )
    & k1_tarski(sK3) = k2_xboole_0(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK5
        | sK4 != k1_tarski(sK3) )
      & ( sK5 != k1_tarski(sK3)
        | k1_xboole_0 != sK4 )
      & ( sK5 != k1_tarski(sK3)
        | sK4 != k1_tarski(sK3) )
      & k1_tarski(sK3) = k2_xboole_0(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f172,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f167,f55])).

% (11575)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f167,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(trivial_inequality_removal,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f68,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f622,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f552,f97,f88])).

fof(f97,plain,
    ( spl9_3
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f552,plain,
    ( k1_xboole_0 = sK4
    | sK4 = k1_tarski(sK3) ),
    inference(resolution,[],[f65,f165])).

fof(f165,plain,(
    r1_tarski(sK4,k1_tarski(sK3)) ),
    inference(trivial_inequality_removal,[],[f160])).

fof(f160,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK4,k1_tarski(sK3)) ),
    inference(superposition,[],[f68,f117])).

fof(f117,plain,(
    k1_xboole_0 = k4_xboole_0(sK4,k1_tarski(sK3)) ),
    inference(superposition,[],[f54,f46])).

fof(f616,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f614,f90])).

fof(f90,plain,
    ( sK4 != k1_tarski(sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f614,plain,
    ( sK4 = k1_tarski(sK3)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f591,f119])).

fof(f119,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f591,plain,
    ( k1_tarski(sK3) = k2_xboole_0(k1_xboole_0,sK4)
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f494,f93])).

fof(f93,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f494,plain,(
    k1_tarski(sK3) = k2_xboole_0(sK5,sK4) ),
    inference(resolution,[],[f469,f123])).

fof(f123,plain,(
    ! [X4,X3] : sP2(X3,X4,k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f86,f55])).

fof(f86,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f23,f22])).

fof(f22,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f469,plain,(
    ! [X17] :
      ( ~ sP2(sK4,sK5,X17)
      | k1_tarski(sK3) = X17 ) ),
    inference(superposition,[],[f80,f46])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,
    ( ~ spl9_5
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f106,f88,f108])).

% (11563)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f106,plain,
    ( sK4 != k1_tarski(sK3)
    | sK4 != sK5 ),
    inference(inner_rewriting,[],[f105])).

fof(f105,plain,
    ( sK5 != k1_tarski(sK3)
    | sK4 != sK5 ),
    inference(inner_rewriting,[],[f47])).

fof(f47,plain,
    ( sK5 != k1_tarski(sK3)
    | sK4 != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f48,f101,f97])).

fof(f48,plain,
    ( sK5 != k1_tarski(sK3)
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f49,f92,f88])).

fof(f49,plain,
    ( k1_xboole_0 != sK5
    | sK4 != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (11577)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (11562)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (11559)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (11566)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (11569)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.56  % (11561)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.56  % (11559)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f661,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f95,f104,f111,f616,f622,f627,f660])).
% 0.20/0.56  fof(f660,plain,(
% 0.20/0.56    ~spl9_1 | ~spl9_4 | spl9_5),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f659])).
% 0.20/0.56  fof(f659,plain,(
% 0.20/0.56    $false | (~spl9_1 | ~spl9_4 | spl9_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f658,f110])).
% 0.20/0.56  fof(f110,plain,(
% 0.20/0.56    sK4 != sK5 | spl9_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f108])).
% 0.20/0.56  % (11579)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.56  fof(f108,plain,(
% 0.20/0.56    spl9_5 <=> sK4 = sK5),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.56  fof(f658,plain,(
% 0.20/0.56    sK4 = sK5 | (~spl9_1 | ~spl9_4)),
% 0.20/0.56    inference(forward_demodulation,[],[f102,f89])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    sK4 = k1_tarski(sK3) | ~spl9_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f88])).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    spl9_1 <=> sK4 = k1_tarski(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    sK5 = k1_tarski(sK3) | ~spl9_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f101])).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    spl9_4 <=> sK5 = k1_tarski(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.56  fof(f627,plain,(
% 0.20/0.56    spl9_4 | spl9_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f626,f92,f101])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    spl9_2 <=> k1_xboole_0 = sK5),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.56  fof(f626,plain,(
% 0.20/0.56    sK5 = k1_tarski(sK3) | spl9_2),
% 0.20/0.56    inference(subsumption_resolution,[],[f624,f94])).
% 0.20/0.56  % (11570)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    k1_xboole_0 != sK5 | spl9_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f92])).
% 0.20/0.56  fof(f624,plain,(
% 0.20/0.56    k1_xboole_0 = sK5 | sK5 = k1_tarski(sK3)),
% 0.20/0.56    inference(resolution,[],[f176,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.56    inference(flattening,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.56  fof(f176,plain,(
% 0.20/0.56    r1_tarski(sK5,k1_tarski(sK3))),
% 0.20/0.56    inference(superposition,[],[f172,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    k1_tarski(sK3) = k2_xboole_0(sK4,sK5)),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    (k1_xboole_0 != sK5 | sK4 != k1_tarski(sK3)) & (sK5 != k1_tarski(sK3) | k1_xboole_0 != sK4) & (sK5 != k1_tarski(sK3) | sK4 != k1_tarski(sK3)) & k1_tarski(sK3) = k2_xboole_0(sK4,sK5)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK5 | sK4 != k1_tarski(sK3)) & (sK5 != k1_tarski(sK3) | k1_xboole_0 != sK4) & (sK5 != k1_tarski(sK3) | sK4 != k1_tarski(sK3)) & k1_tarski(sK3) = k2_xboole_0(sK4,sK5))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.56    inference(negated_conjecture,[],[f14])).
% 0.20/0.56  fof(f14,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.56  fof(f172,plain,(
% 0.20/0.56    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.20/0.56    inference(superposition,[],[f167,f55])).
% 0.20/0.56  % (11575)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f158])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(superposition,[],[f68,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.56  fof(f622,plain,(
% 0.20/0.56    spl9_1 | spl9_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f552,f97,f88])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    spl9_3 <=> k1_xboole_0 = sK4),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.56  fof(f552,plain,(
% 0.20/0.56    k1_xboole_0 = sK4 | sK4 = k1_tarski(sK3)),
% 0.20/0.56    inference(resolution,[],[f65,f165])).
% 0.20/0.56  fof(f165,plain,(
% 0.20/0.56    r1_tarski(sK4,k1_tarski(sK3))),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f160])).
% 0.20/0.56  fof(f160,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK4,k1_tarski(sK3))),
% 0.20/0.56    inference(superposition,[],[f68,f117])).
% 0.20/0.56  fof(f117,plain,(
% 0.20/0.56    k1_xboole_0 = k4_xboole_0(sK4,k1_tarski(sK3))),
% 0.20/0.56    inference(superposition,[],[f54,f46])).
% 0.20/0.56  fof(f616,plain,(
% 0.20/0.56    spl9_1 | ~spl9_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f615])).
% 0.20/0.56  fof(f615,plain,(
% 0.20/0.56    $false | (spl9_1 | ~spl9_2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f614,f90])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    sK4 != k1_tarski(sK3) | spl9_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f88])).
% 0.20/0.56  fof(f614,plain,(
% 0.20/0.56    sK4 = k1_tarski(sK3) | ~spl9_2),
% 0.20/0.56    inference(forward_demodulation,[],[f591,f119])).
% 0.20/0.56  fof(f119,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.56    inference(superposition,[],[f55,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.56  fof(f591,plain,(
% 0.20/0.56    k1_tarski(sK3) = k2_xboole_0(k1_xboole_0,sK4) | ~spl9_2),
% 0.20/0.56    inference(backward_demodulation,[],[f494,f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    k1_xboole_0 = sK5 | ~spl9_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f92])).
% 0.20/0.56  fof(f494,plain,(
% 0.20/0.56    k1_tarski(sK3) = k2_xboole_0(sK5,sK4)),
% 0.20/0.56    inference(resolution,[],[f469,f123])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    ( ! [X4,X3] : (sP2(X3,X4,k2_xboole_0(X4,X3))) )),
% 0.20/0.56    inference(superposition,[],[f86,f55])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sP2(X0,X1,k2_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(equality_resolution,[],[f79])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.56    inference(nnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.20/0.56    inference(definition_folding,[],[f2,f23,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.56  fof(f469,plain,(
% 0.20/0.56    ( ! [X17] : (~sP2(sK4,sK5,X17) | k1_tarski(sK3) = X17) )),
% 0.20/0.56    inference(superposition,[],[f80,f46])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f45])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ~spl9_5 | ~spl9_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f106,f88,f108])).
% 0.20/0.56  % (11563)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    sK4 != k1_tarski(sK3) | sK4 != sK5),
% 0.20/0.56    inference(inner_rewriting,[],[f105])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    sK5 != k1_tarski(sK3) | sK4 != sK5),
% 0.20/0.56    inference(inner_rewriting,[],[f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    sK5 != k1_tarski(sK3) | sK4 != k1_tarski(sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ~spl9_3 | ~spl9_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f48,f101,f97])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    sK5 != k1_tarski(sK3) | k1_xboole_0 != sK4),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    ~spl9_1 | ~spl9_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f49,f92,f88])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    k1_xboole_0 != sK5 | sK4 != k1_tarski(sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (11559)------------------------------
% 0.20/0.56  % (11559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (11559)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (11559)Memory used [KB]: 6396
% 0.20/0.56  % (11559)Time elapsed: 0.116 s
% 0.20/0.56  % (11559)------------------------------
% 0.20/0.56  % (11559)------------------------------
% 0.20/0.57  % (11548)Success in time 0.205 s
%------------------------------------------------------------------------------
