%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (  93 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    6
%              Number of atoms          :  147 ( 218 expanded)
%              Number of equality atoms :   36 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f48,f56,f65,f69,f73,f116,f146,f180,f331,f336,f365])).

fof(f365,plain,
    ( ~ spl3_1
    | spl3_16
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl3_1
    | spl3_16
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f145,f337])).

fof(f337,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,X0))
    | ~ spl3_1
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f34,f335])).

fof(f335,plain,
    ( ! [X4,X2,X3] :
        ( k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(X3,X4))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl3_32
  <=> ! [X3,X2,X4] :
        ( k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(X3,X4))
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f34,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f145,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f336,plain,
    ( spl3_32
    | ~ spl3_6
    | ~ spl3_21
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f332,f329,f178,f54,f334])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f178,plain,
    ( spl3_21
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f329,plain,
    ( spl3_31
  <=> ! [X3,X2,X4] :
        ( k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f332,plain,
    ( ! [X4,X2,X3] :
        ( k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(X3,X4))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_6
    | ~ spl3_21
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f330,f182])).

fof(f182,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f55,f179])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f55,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f330,plain,
    ( ! [X4,X2,X3] :
        ( k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f329])).

fof(f331,plain,
    ( spl3_31
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f118,f114,f67,f329])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f114,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f118,plain,
    ( ! [X4,X2,X3] :
        ( k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(superposition,[],[f115,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f115,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f180,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f91,f63,f46,f178])).

fof(f46,plain,
    ( spl3_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f64,f47])).

fof(f47,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f146,plain,
    ( ~ spl3_16
    | spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f98,f71,f37,f143])).

fof(f37,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f98,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f39,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f39,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f116,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f30,f114])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f73,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f56,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f40,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (23846)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (23838)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (23840)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (23839)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (23850)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (23841)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (23840)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (23845)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f368,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f35,f40,f48,f56,f65,f69,f73,f116,f146,f180,f331,f336,f365])).
% 0.20/0.49  fof(f365,plain,(
% 0.20/0.49    ~spl3_1 | spl3_16 | ~spl3_32),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f364])).
% 0.20/0.49  fof(f364,plain,(
% 0.20/0.49    $false | (~spl3_1 | spl3_16 | ~spl3_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f145,f337])).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,X0))) ) | (~spl3_1 | ~spl3_32)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f34,f335])).
% 0.20/0.49  fof(f335,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X2,X3)) ) | ~spl3_32),
% 0.20/0.49    inference(avatar_component_clause,[],[f334])).
% 0.20/0.49  fof(f334,plain,(
% 0.20/0.49    spl3_32 <=> ! [X3,X2,X4] : (k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X2,X3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl3_16 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f336,plain,(
% 0.20/0.49    spl3_32 | ~spl3_6 | ~spl3_21 | ~spl3_31),
% 0.20/0.49    inference(avatar_split_clause,[],[f332,f329,f178,f54,f334])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl3_21 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f329,plain,(
% 0.20/0.49    spl3_31 <=> ! [X3,X2,X4] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(X2,X3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.49  fof(f332,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X2,X3)) ) | (~spl3_6 | ~spl3_21 | ~spl3_31)),
% 0.20/0.49    inference(forward_demodulation,[],[f330,f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl3_6 | ~spl3_21)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f55,f179])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f178])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f330,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(X2,X3)) ) | ~spl3_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f329])).
% 0.20/0.49  fof(f331,plain,(
% 0.20/0.49    spl3_31 | ~spl3_9 | ~spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f118,f114,f67,f329])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl3_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl3_14 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(X2,X3)) ) | (~spl3_9 | ~spl3_14)),
% 0.20/0.49    inference(superposition,[],[f115,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl3_21 | ~spl3_4 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f91,f63,f46,f178])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl3_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl3_8 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_8)),
% 0.20/0.49    inference(superposition,[],[f64,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f46])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ~spl3_16 | spl3_2 | ~spl3_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f98,f71,f37,f143])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl3_10 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (spl3_2 | ~spl3_10)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f39,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f37])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f114])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl3_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f71])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f67])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f63])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f54])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f21,f46])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f37])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f18,f32])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (23840)------------------------------
% 0.20/0.49  % (23840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23840)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (23840)Memory used [KB]: 6268
% 0.20/0.49  % (23840)Time elapsed: 0.073 s
% 0.20/0.49  % (23840)------------------------------
% 0.20/0.49  % (23840)------------------------------
% 0.20/0.49  % (23849)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (23834)Success in time 0.137 s
%------------------------------------------------------------------------------
