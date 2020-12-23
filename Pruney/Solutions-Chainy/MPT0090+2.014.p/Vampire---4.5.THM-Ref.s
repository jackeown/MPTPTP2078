%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  58 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 125 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f43,f67])).

fof(f67,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f35,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_2
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(forward_demodulation,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f64,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f59,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f59,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f22,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f43,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f41,f39])).

fof(f39,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( sK0 != sK0
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f17,f36])).

fof(f36,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f17,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
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

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f41,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f19,f36])).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f37,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f16,f34,f30])).

fof(f16,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.42  % (16017)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.42  % (16024)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.43  % (16017)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f37,f43,f67])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    ~spl2_1 | spl2_2),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    $false | (~spl2_1 | spl2_2)),
% 0.22/0.43    inference(subsumption_resolution,[],[f65,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    sK0 != k4_xboole_0(sK0,sK1) | spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl2_2 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_1),
% 0.22/0.43    inference(forward_demodulation,[],[f64,f44])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.22/0.43    inference(resolution,[],[f28,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.43    inference(forward_demodulation,[],[f23,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl2_1),
% 0.22/0.43    inference(forward_demodulation,[],[f59,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl2_1),
% 0.22/0.43    inference(superposition,[],[f22,f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_1),
% 0.22/0.43    inference(resolution,[],[f27,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    r1_xboole_0(sK0,sK1) | ~spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f24,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ~spl2_2),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    $false | ~spl2_2),
% 0.22/0.43    inference(subsumption_resolution,[],[f41,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ~r1_xboole_0(sK0,sK1) | ~spl2_2),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    sK0 != sK0 | ~r1_xboole_0(sK0,sK1) | ~spl2_2),
% 0.22/0.43    inference(backward_demodulation,[],[f17,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.43    inference(negated_conjecture,[],[f8])).
% 0.22/0.43  fof(f8,conjecture,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    r1_xboole_0(sK0,sK1) | ~spl2_2),
% 0.22/0.43    inference(superposition,[],[f19,f36])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl2_1 | spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f34,f30])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (16017)------------------------------
% 0.22/0.43  % (16017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (16017)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (16017)Memory used [KB]: 10618
% 0.22/0.43  % (16017)Time elapsed: 0.044 s
% 0.22/0.43  % (16017)------------------------------
% 0.22/0.43  % (16017)------------------------------
% 0.22/0.43  % (16007)Success in time 0.072 s
%------------------------------------------------------------------------------
