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
% DateTime   : Thu Dec  3 12:37:52 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 128 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  203 ( 492 expanded)
%              Number of equality atoms :   96 ( 347 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f56,f63,f89,f113,f122,f127,f133,f162])).

fof(f162,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f153,f62])).

fof(f62,plain,
    ( sK1 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f153,plain,
    ( sK1 = sK2
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f41,f54])).

fof(f54,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f133,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f131,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl3_4
    | spl3_8 ),
    inference(forward_demodulation,[],[f130,f54])).

fof(f130,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl3_4
    | spl3_8 ),
    inference(resolution,[],[f128,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ r1_tarski(k1_tarski(sK0),X0) ) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

% (20742)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f128,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl3_4
    | spl3_8 ),
    inference(forward_demodulation,[],[f126,f54])).

fof(f126,plain,
    ( ~ r1_tarski(sK1,k1_tarski(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_8
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( ~ spl3_8
    | spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f83,f40,f49,f124])).

fof(f49,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k1_tarski(sK0))
    | spl3_1 ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(sK0)) )
    | spl3_1 ),
    inference(superposition,[],[f42,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f42,plain,
    ( sK1 != k1_tarski(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f122,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f118,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f118,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f21,f45])).

fof(f45,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f109,f35])).

fof(f35,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | spl3_7 ),
    inference(superposition,[],[f94,f21])).

fof(f94,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,sK2),k1_tarski(sK0))
    | spl3_7 ),
    inference(superposition,[],[f90,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f90,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k1_tarski(sK0))
    | spl3_7 ),
    inference(resolution,[],[f88,f31])).

fof(f88,plain,
    ( ~ r1_tarski(sK2,k1_tarski(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_7
  <=> r1_tarski(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f89,plain,
    ( ~ spl3_7
    | spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f84,f53,f44,f86])).

fof(f84,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,k1_tarski(sK0))
    | spl3_4 ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,
    ( ! [X0] :
        ( sK2 != X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(sK0)) )
    | spl3_4 ),
    inference(superposition,[],[f55,f25])).

fof(f55,plain,
    ( sK2 != k1_tarski(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f63,plain,
    ( ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f58,f40,f60])).

fof(f58,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f57])).

fof(f57,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f22])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f23,f53,f49])).

fof(f23,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f44,f40])).

fof(f24,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:37:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.08/0.52  % (20726)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.08/0.52  % (20740)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.08/0.52  % (20744)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.08/0.52  % (20720)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.08/0.53  % (20736)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.08/0.53  % (20736)Refutation not found, incomplete strategy% (20736)------------------------------
% 1.08/0.53  % (20736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.53  % (20736)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.53  
% 1.08/0.53  % (20736)Memory used [KB]: 1663
% 1.08/0.53  % (20736)Time elapsed: 0.069 s
% 1.08/0.53  % (20736)------------------------------
% 1.08/0.53  % (20736)------------------------------
% 1.08/0.53  % (20730)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.08/0.53  % (20723)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.08/0.53  % (20737)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.53  % (20724)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.53  % (20730)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f163,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(avatar_sat_refutation,[],[f47,f56,f63,f89,f113,f122,f127,f133,f162])).
% 1.30/0.53  fof(f162,plain,(
% 1.30/0.53    ~spl3_1 | ~spl3_4 | spl3_5),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f161])).
% 1.30/0.53  fof(f161,plain,(
% 1.30/0.53    $false | (~spl3_1 | ~spl3_4 | spl3_5)),
% 1.30/0.53    inference(subsumption_resolution,[],[f153,f62])).
% 1.30/0.53  fof(f62,plain,(
% 1.30/0.53    sK1 != sK2 | spl3_5),
% 1.30/0.53    inference(avatar_component_clause,[],[f60])).
% 1.30/0.53  fof(f60,plain,(
% 1.30/0.53    spl3_5 <=> sK1 = sK2),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.30/0.53  fof(f153,plain,(
% 1.30/0.53    sK1 = sK2 | (~spl3_1 | ~spl3_4)),
% 1.30/0.53    inference(superposition,[],[f41,f54])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    sK2 = k1_tarski(sK0) | ~spl3_4),
% 1.30/0.53    inference(avatar_component_clause,[],[f53])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    spl3_4 <=> sK2 = k1_tarski(sK0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    sK1 = k1_tarski(sK0) | ~spl3_1),
% 1.30/0.53    inference(avatar_component_clause,[],[f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    spl3_1 <=> sK1 = k1_tarski(sK0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.30/0.53  fof(f133,plain,(
% 1.30/0.53    ~spl3_4 | spl3_8),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f132])).
% 1.30/0.53  fof(f132,plain,(
% 1.30/0.53    $false | (~spl3_4 | spl3_8)),
% 1.30/0.53    inference(subsumption_resolution,[],[f131,f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.30/0.53    inference(equality_resolution,[],[f32])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.30/0.53    inference(cnf_transformation,[],[f20])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.53    inference(flattening,[],[f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.53    inference(nnf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.30/0.53  fof(f131,plain,(
% 1.30/0.53    ~r1_tarski(sK2,sK2) | (~spl3_4 | spl3_8)),
% 1.30/0.53    inference(forward_demodulation,[],[f130,f54])).
% 1.30/0.53  fof(f130,plain,(
% 1.30/0.53    ~r1_tarski(k1_tarski(sK0),sK2) | (~spl3_4 | spl3_8)),
% 1.30/0.53    inference(resolution,[],[f128,f66])).
% 1.30/0.53  fof(f66,plain,(
% 1.30/0.53    ( ! [X0] : (r1_tarski(sK1,X0) | ~r1_tarski(k1_tarski(sK0),X0)) )),
% 1.30/0.53    inference(superposition,[],[f31,f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f16])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.54  % (20742)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.54  fof(f13,plain,(
% 1.30/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,negated_conjecture,(
% 1.30/0.54    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.30/0.54    inference(negated_conjecture,[],[f11])).
% 1.30/0.54  fof(f11,conjecture,(
% 1.30/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f14])).
% 1.30/0.54  fof(f14,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.30/0.54    inference(ennf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.30/0.54  fof(f128,plain,(
% 1.30/0.54    ~r1_tarski(sK1,sK2) | (~spl3_4 | spl3_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f126,f54])).
% 1.30/0.54  fof(f126,plain,(
% 1.30/0.54    ~r1_tarski(sK1,k1_tarski(sK0)) | spl3_8),
% 1.30/0.54    inference(avatar_component_clause,[],[f124])).
% 1.30/0.54  fof(f124,plain,(
% 1.30/0.54    spl3_8 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.30/0.54  fof(f127,plain,(
% 1.30/0.54    ~spl3_8 | spl3_3 | spl3_1),
% 1.30/0.54    inference(avatar_split_clause,[],[f83,f40,f49,f124])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    spl3_3 <=> k1_xboole_0 = sK1),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    k1_xboole_0 = sK1 | ~r1_tarski(sK1,k1_tarski(sK0)) | spl3_1),
% 1.30/0.54    inference(equality_resolution,[],[f64])).
% 1.30/0.54  fof(f64,plain,(
% 1.30/0.54    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(sK0))) ) | spl3_1),
% 1.30/0.54    inference(superposition,[],[f42,f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.30/0.54    inference(flattening,[],[f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.30/0.54    inference(nnf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    sK1 != k1_tarski(sK0) | spl3_1),
% 1.30/0.54    inference(avatar_component_clause,[],[f40])).
% 1.30/0.54  fof(f122,plain,(
% 1.30/0.54    spl3_1 | ~spl3_2),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f121])).
% 1.30/0.54  fof(f121,plain,(
% 1.30/0.54    $false | (spl3_1 | ~spl3_2)),
% 1.30/0.54    inference(subsumption_resolution,[],[f120,f42])).
% 1.30/0.54  fof(f120,plain,(
% 1.30/0.54    sK1 = k1_tarski(sK0) | ~spl3_2),
% 1.30/0.54    inference(forward_demodulation,[],[f118,f28])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.30/0.54  fof(f118,plain,(
% 1.30/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_2),
% 1.30/0.54    inference(superposition,[],[f21,f45])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    k1_xboole_0 = sK2 | ~spl3_2),
% 1.30/0.54    inference(avatar_component_clause,[],[f44])).
% 1.30/0.54  fof(f44,plain,(
% 1.30/0.54    spl3_2 <=> k1_xboole_0 = sK2),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.30/0.54  fof(f113,plain,(
% 1.30/0.54    spl3_7),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f112])).
% 1.30/0.54  fof(f112,plain,(
% 1.30/0.54    $false | spl3_7),
% 1.30/0.54    inference(subsumption_resolution,[],[f109,f35])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 1.30/0.54    inference(equality_resolution,[],[f27])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f18])).
% 1.30/0.54  fof(f109,plain,(
% 1.30/0.54    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) | spl3_7),
% 1.30/0.54    inference(superposition,[],[f94,f21])).
% 1.30/0.54  fof(f94,plain,(
% 1.30/0.54    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,sK2),k1_tarski(sK0))) ) | spl3_7),
% 1.30/0.54    inference(superposition,[],[f90,f29])).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k1_tarski(sK0))) ) | spl3_7),
% 1.30/0.54    inference(resolution,[],[f88,f31])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    ~r1_tarski(sK2,k1_tarski(sK0)) | spl3_7),
% 1.30/0.54    inference(avatar_component_clause,[],[f86])).
% 1.30/0.54  fof(f86,plain,(
% 1.30/0.54    spl3_7 <=> r1_tarski(sK2,k1_tarski(sK0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.30/0.54  fof(f89,plain,(
% 1.30/0.54    ~spl3_7 | spl3_2 | spl3_4),
% 1.30/0.54    inference(avatar_split_clause,[],[f84,f53,f44,f86])).
% 1.30/0.54  fof(f84,plain,(
% 1.30/0.54    k1_xboole_0 = sK2 | ~r1_tarski(sK2,k1_tarski(sK0)) | spl3_4),
% 1.30/0.54    inference(equality_resolution,[],[f65])).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X0] : (sK2 != X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(sK0))) ) | spl3_4),
% 1.30/0.54    inference(superposition,[],[f55,f25])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    sK2 != k1_tarski(sK0) | spl3_4),
% 1.30/0.54    inference(avatar_component_clause,[],[f53])).
% 1.30/0.54  fof(f63,plain,(
% 1.30/0.54    ~spl3_5 | ~spl3_1),
% 1.30/0.54    inference(avatar_split_clause,[],[f58,f40,f60])).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 1.30/0.54    inference(inner_rewriting,[],[f57])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 1.30/0.54    inference(inner_rewriting,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    ~spl3_3 | ~spl3_4),
% 1.30/0.54    inference(avatar_split_clause,[],[f23,f53,f49])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ~spl3_1 | ~spl3_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f24,f44,f40])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (20730)------------------------------
% 1.30/0.54  % (20730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (20730)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (20730)Memory used [KB]: 10746
% 1.30/0.54  % (20730)Time elapsed: 0.114 s
% 1.30/0.54  % (20730)------------------------------
% 1.30/0.54  % (20730)------------------------------
% 1.30/0.54  % (20717)Success in time 0.161 s
%------------------------------------------------------------------------------
