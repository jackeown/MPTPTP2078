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
% DateTime   : Thu Dec  3 12:38:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 307 expanded)
%              Number of leaves         :   15 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  166 ( 618 expanded)
%              Number of equality atoms :  105 ( 523 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f67,f68,f141,f142,f175])).

fof(f175,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f144,f163])).

fof(f163,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f154,f56])).

fof(f56,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f154,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f143,f101])).

fof(f101,plain,(
    ! [X2] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = X2 ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f79,f41])).

fof(f41,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f79,plain,(
    ! [X6,X5] : r1_tarski(X5,k3_tarski(k2_enumset1(X6,X6,X6,X5))) ),
    inference(resolution,[],[f47,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f42,f41])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f143,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f40,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f19,f36,f35])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f34])).

% (28617)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f144,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f53,f61])).

fof(f53,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f142,plain,
    ( spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f140,f55,f64])).

fof(f64,plain,
    ( spl3_4
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f140,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f46,f92])).

fof(f92,plain,(
    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f79,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f29,f36,f36])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f141,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f139,f60,f51])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f46,f69])).

fof(f69,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f42,f40])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f39,f64,f51])).

fof(f39,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f36,f36])).

fof(f20,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f38,f64,f60])).

fof(f38,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f21,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f55,f51])).

fof(f37,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f36])).

fof(f22,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (28619)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (28612)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (28613)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (28615)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (28624)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (28628)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (28624)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (28621)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f58,f67,f68,f141,f142,f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.51    inference(superposition,[],[f144,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl3_2 | ~spl3_3)),
% 0.21/0.51    inference(backward_demodulation,[],[f154,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl3_2 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_3),
% 0.21/0.51    inference(forward_demodulation,[],[f143,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = X2) )),
% 0.21/0.51    inference(resolution,[],[f94,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 0.21/0.51    inference(definition_unfolding,[],[f28,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f26,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f79,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f35])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X6,X5] : (r1_tarski(X5,k3_tarski(k2_enumset1(X6,X6,X6,X5)))) )),
% 0.21/0.51    inference(resolution,[],[f47,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f42,f41])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f25,f35])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f33,f35])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | ~spl3_3),
% 0.21/0.51    inference(backward_demodulation,[],[f40,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl3_3 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f36,f35])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f34])).
% 0.21/0.51  % (28617)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_3)),
% 0.21/0.51    inference(backward_demodulation,[],[f53,f61])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl3_1 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl3_4 | spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f140,f55,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl3_4 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(resolution,[],[f46,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.51    inference(superposition,[],[f79,f40])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f36,f36])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl3_1 | spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f139,f60,f51])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(resolution,[],[f46,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.51    inference(superposition,[],[f42,f40])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f64,f51])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(definition_unfolding,[],[f20,f36,f36])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f64,f60])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f36])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f55,f51])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f36])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28624)------------------------------
% 0.21/0.51  % (28624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28630)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (28624)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28624)Memory used [KB]: 6268
% 0.21/0.51  % (28624)Time elapsed: 0.112 s
% 0.21/0.51  % (28624)------------------------------
% 0.21/0.51  % (28624)------------------------------
% 0.21/0.51  % (28620)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (28620)Refutation not found, incomplete strategy% (28620)------------------------------
% 0.21/0.51  % (28620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28620)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28620)Memory used [KB]: 10746
% 0.21/0.51  % (28620)Time elapsed: 0.117 s
% 0.21/0.51  % (28620)------------------------------
% 0.21/0.51  % (28620)------------------------------
% 0.21/0.52  % (28611)Success in time 0.16 s
%------------------------------------------------------------------------------
