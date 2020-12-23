%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 ( 251 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f56,f62,f70,f81,f215,f236])).

fof(f236,plain,
    ( spl4_3
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f224,f211,f47])).

fof(f47,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f211,plain,
    ( spl4_20
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f224,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f222])).

fof(f222,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl4_20 ),
    inference(superposition,[],[f32,f213])).

fof(f213,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f211])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f215,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f203,f78,f59,f53,f211])).

fof(f53,plain,
    ( spl4_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f59,plain,
    ( spl4_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f78,plain,
    ( spl4_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f203,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f61,f177])).

fof(f177,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(X0,sK2))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f175,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f175,plain,
    ( ! [X1] : k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k3_xboole_0(sK2,X1))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f171,f168])).

fof(f168,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f63,f107])).

fof(f107,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f105,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f105,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
    | ~ spl4_7 ),
    inference(superposition,[],[f35,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f63,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl4_4 ),
    inference(superposition,[],[f35,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f171,plain,
    ( ! [X1] : k3_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK2,X1))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f168,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f61,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f81,plain,
    ( spl4_7
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f76,f67,f53,f78])).

fof(f67,plain,
    ( spl4_6
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f71,f55])).

fof(f71,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)
    | ~ spl4_6 ),
    inference(superposition,[],[f27,f69])).

fof(f69,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f65,f53,f67])).

fof(f65,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f64,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f64,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f28,f55])).

fof(f62,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f57,f37,f59])).

fof(f37,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f56,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f51,f42,f53])).

fof(f42,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f44,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f50,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f23,f37])).

fof(f23,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (21946)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (21945)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (21955)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (21948)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (21961)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (21953)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (21947)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (21956)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (21949)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (21956)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (21958)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (21951)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f237,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f40,f45,f50,f56,f62,f70,f81,f215,f236])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    spl4_3 | ~spl4_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f224,f211,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl4_3 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    spl4_20 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK1) | ~spl4_20),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f222])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl4_20),
% 0.20/0.49    inference(superposition,[],[f32,f213])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f211])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    spl4_20 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f203,f78,f59,f53,f211])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl4_4 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl4_5 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl4_7 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.49    inference(superposition,[],[f61,f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(X0,sK2))) ) | (~spl4_4 | ~spl4_7)),
% 0.20/0.49    inference(superposition,[],[f175,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ( ! [X1] : (k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k3_xboole_0(sK2,X1))) ) | (~spl4_4 | ~spl4_7)),
% 0.20/0.49    inference(forward_demodulation,[],[f171,f168])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0)) ) | (~spl4_4 | ~spl4_7)),
% 0.20/0.49    inference(forward_demodulation,[],[f63,f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X0] : (k3_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | ~spl4_7),
% 0.20/0.49    inference(forward_demodulation,[],[f105,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ) | ~spl4_7),
% 0.20/0.49    inference(superposition,[],[f35,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f78])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | ~spl4_4),
% 0.20/0.49    inference(superposition,[],[f35,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f53])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    ( ! [X1] : (k3_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK2,X1))) ) | (~spl4_4 | ~spl4_7)),
% 0.20/0.49    inference(superposition,[],[f168,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl4_7 | ~spl4_4 | ~spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f76,f67,f53,f78])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl4_6 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl4_4 | ~spl4_6)),
% 0.20/0.49    inference(forward_demodulation,[],[f71,f55])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) | ~spl4_6),
% 0.20/0.49    inference(superposition,[],[f27,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl4_6 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f65,f53,f67])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_4),
% 0.20/0.49    inference(forward_demodulation,[],[f64,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~spl4_4),
% 0.20/0.49    inference(superposition,[],[f28,f55])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl4_5 | ~spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f57,f37,f59])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    spl4_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f39,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f37])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl4_4 | ~spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f42,f53])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    spl4_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl4_2),
% 0.20/0.49    inference(resolution,[],[f44,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    r1_tarski(sK0,sK2) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f42])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f21,f47])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f22,f42])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    r1_tarski(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f37])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (21956)------------------------------
% 0.20/0.49  % (21956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21956)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (21956)Memory used [KB]: 10746
% 0.20/0.49  % (21956)Time elapsed: 0.078 s
% 0.20/0.49  % (21956)------------------------------
% 0.20/0.49  % (21956)------------------------------
% 0.20/0.50  % (21944)Success in time 0.138 s
%------------------------------------------------------------------------------
