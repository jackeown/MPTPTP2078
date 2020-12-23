%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 209 expanded)
%              Number of leaves         :   14 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  159 ( 516 expanded)
%              Number of equality atoms :  101 ( 437 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f62,f63,f74,f82,f94])).

fof(f94,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f88])).

fof(f88,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f76,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f83,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f83,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f77,f51])).

fof(f51,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f36,f56])).

fof(f56,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f36,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(definition_unfolding,[],[f17,f32,f25])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

% (19501)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f17,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
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

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f76,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f48,f56])).

fof(f48,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_1
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f80,f59,f50])).

fof(f59,plain,
    ( spl3_4
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f80,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f68,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k2_enumset1(sK0,sK0,sK0,sK0) = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f41,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f42,f36])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f26,f32,f32])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f74,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f73,f55,f46])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f41,f64])).

fof(f64,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f38,f36])).

fof(f63,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f35,f59,f46])).

fof(f35,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f18,f32,f32])).

fof(f18,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f34,f59,f55])).

fof(f34,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f19,f32])).

fof(f19,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f50,f46])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f32])).

fof(f20,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (19473)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (19484)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (19485)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (19482)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (19474)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (19485)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f53,f62,f63,f74,f82,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(superposition,[],[f76,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f83,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(backward_demodulation,[],[f77,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl3_2 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.32/0.53  fof(f77,plain,(
% 1.32/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) | ~spl3_3),
% 1.32/0.53    inference(backward_demodulation,[],[f36,f56])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    k1_xboole_0 = sK1 | ~spl3_3),
% 1.32/0.53    inference(avatar_component_clause,[],[f55])).
% 1.32/0.53  fof(f55,plain,(
% 1.32/0.53    spl3_3 <=> k1_xboole_0 = sK1),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 1.32/0.53    inference(definition_unfolding,[],[f17,f32,f25])).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f22,f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f24,f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.53  % (19501)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,plain,(
% 1.32/0.53    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 1.32/0.53  fof(f13,plain,(
% 1.32/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f11,plain,(
% 1.32/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.32/0.53    inference(ennf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.32/0.53    inference(negated_conjecture,[],[f9])).
% 1.32/0.53  fof(f9,conjecture,(
% 1.32/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.32/0.53  fof(f76,plain,(
% 1.32/0.53    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_3)),
% 1.32/0.53    inference(backward_demodulation,[],[f48,f56])).
% 1.32/0.53  fof(f48,plain,(
% 1.32/0.53    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_1),
% 1.32/0.53    inference(avatar_component_clause,[],[f46])).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    spl3_1 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.32/0.53  fof(f82,plain,(
% 1.32/0.53    spl3_2 | spl3_4),
% 1.32/0.53    inference(avatar_split_clause,[],[f80,f59,f50])).
% 1.32/0.53  fof(f59,plain,(
% 1.32/0.53    spl3_4 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.32/0.53  fof(f80,plain,(
% 1.32/0.53    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 1.32/0.53    inference(resolution,[],[f68,f65])).
% 1.32/0.53  fof(f65,plain,(
% 1.32/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.32/0.53    inference(superposition,[],[f38,f37])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f23,f25])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.32/0.53  fof(f68,plain,(
% 1.32/0.53    ( ! [X0] : (~r1_tarski(X0,sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = X0 | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(resolution,[],[f41,f66])).
% 1.32/0.53  fof(f66,plain,(
% 1.32/0.53    ( ! [X0] : (r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_tarski(X0,sK2)) )),
% 1.32/0.53    inference(superposition,[],[f42,f36])).
% 1.32/0.53  fof(f42,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f30,f25])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,plain,(
% 1.32/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.32/0.53    inference(definition_unfolding,[],[f26,f32,f32])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f16])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.32/0.53    inference(flattening,[],[f15])).
% 1.32/0.53  fof(f15,plain,(
% 1.32/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.32/0.53    inference(nnf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.32/0.53  fof(f74,plain,(
% 1.32/0.53    spl3_1 | spl3_3),
% 1.32/0.53    inference(avatar_split_clause,[],[f73,f55,f46])).
% 1.32/0.53  fof(f73,plain,(
% 1.32/0.53    k1_xboole_0 = sK1 | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.32/0.53    inference(resolution,[],[f41,f64])).
% 1.32/0.53  fof(f64,plain,(
% 1.32/0.53    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.32/0.53    inference(superposition,[],[f38,f36])).
% 1.32/0.53  fof(f63,plain,(
% 1.32/0.53    ~spl3_1 | ~spl3_4),
% 1.32/0.53    inference(avatar_split_clause,[],[f35,f59,f46])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.32/0.53    inference(definition_unfolding,[],[f18,f32,f32])).
% 1.32/0.53  fof(f18,plain,(
% 1.32/0.53    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f62,plain,(
% 1.32/0.53    ~spl3_3 | ~spl3_4),
% 1.32/0.53    inference(avatar_split_clause,[],[f34,f59,f55])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.32/0.53    inference(definition_unfolding,[],[f19,f32])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f53,plain,(
% 1.32/0.53    ~spl3_1 | ~spl3_2),
% 1.32/0.53    inference(avatar_split_clause,[],[f33,f50,f46])).
% 1.32/0.53  fof(f33,plain,(
% 1.32/0.53    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.32/0.53    inference(definition_unfolding,[],[f20,f32])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (19485)------------------------------
% 1.32/0.53  % (19485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (19485)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (19485)Memory used [KB]: 6268
% 1.32/0.53  % (19485)Time elapsed: 0.112 s
% 1.32/0.53  % (19485)------------------------------
% 1.32/0.53  % (19485)------------------------------
% 1.32/0.53  % (19472)Success in time 0.174 s
%------------------------------------------------------------------------------
