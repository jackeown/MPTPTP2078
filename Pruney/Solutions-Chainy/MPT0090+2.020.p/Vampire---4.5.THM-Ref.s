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
% DateTime   : Thu Dec  3 12:31:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  74 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 142 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f493,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f30,f34,f475])).

fof(f475,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f28,f473])).

fof(f473,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f424,f15])).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f424,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f110,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f18,f23])).

fof(f23,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f110,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f41,f90])).

fof(f90,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f20,f48])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f45,f15])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f17,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f40,f37])).

fof(f37,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f18,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f16,f15])).

fof(f16,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f17,f15])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f41,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f17,f17])).

fof(f28,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f34,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f24,f31])).

fof(f31,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f16,f27])).

fof(f27,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f24,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f30,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f13,f26,f22])).

fof(f13,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK0 != k4_xboole_0(sK0,sK1)
        | ~ r1_xboole_0(sK0,sK1) )
      & ( sK0 = k4_xboole_0(sK0,sK1)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f29,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f14,f26,f22])).

fof(f14,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:50:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (14598)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.45  % (14598)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f493,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f29,f30,f34,f475])).
% 0.22/0.45  fof(f475,plain,(
% 0.22/0.45    ~spl2_1 | spl2_2),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f474])).
% 0.22/0.45  fof(f474,plain,(
% 0.22/0.45    $false | (~spl2_1 | spl2_2)),
% 0.22/0.45    inference(subsumption_resolution,[],[f28,f473])).
% 0.22/0.45  fof(f473,plain,(
% 0.22/0.45    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_1),
% 0.22/0.45    inference(forward_demodulation,[],[f424,f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.45  fof(f424,plain,(
% 0.22/0.45    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl2_1),
% 0.22/0.45    inference(superposition,[],[f110,f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl2_1),
% 0.22/0.45    inference(resolution,[],[f18,f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    r1_xboole_0(sK0,sK1) | ~spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(nnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(backward_demodulation,[],[f41,f90])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 0.22/0.45    inference(superposition,[],[f20,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.45    inference(forward_demodulation,[],[f45,f15])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(superposition,[],[f17,f44])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(forward_demodulation,[],[f40,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 0.22/0.45    inference(resolution,[],[f18,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.45    inference(superposition,[],[f16,f15])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(superposition,[],[f17,f15])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(superposition,[],[f17,f17])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    sK0 != k4_xboole_0(sK0,sK1) | spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    spl2_2 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    spl2_1 | ~spl2_2),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    $false | (spl2_1 | ~spl2_2)),
% 0.22/0.45    inference(subsumption_resolution,[],[f24,f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    r1_xboole_0(sK0,sK1) | ~spl2_2),
% 0.22/0.45    inference(superposition,[],[f16,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f26])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f22])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    spl2_1 | spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f13,f26,f22])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(nnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ~spl2_1 | ~spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f14,f26,f22])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (14598)------------------------------
% 0.22/0.45  % (14598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (14598)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (14598)Memory used [KB]: 6396
% 0.22/0.45  % (14598)Time elapsed: 0.014 s
% 0.22/0.45  % (14598)------------------------------
% 0.22/0.45  % (14598)------------------------------
% 0.22/0.45  % (14581)Success in time 0.091 s
%------------------------------------------------------------------------------
