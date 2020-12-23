%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  94 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  141 ( 212 expanded)
%              Number of equality atoms :   51 (  85 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f42,f44,f48,f52,f56,f64,f68,f79])).

fof(f79,plain,
    ( ~ spl2_1
    | spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl2_1
    | spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f77,f40])).

fof(f40,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_4
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f77,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f73,f28])).

fof(f28,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f73,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(superposition,[],[f67,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f67,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f68,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f22,f66])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f64,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f59,f50,f35,f61])).

fof(f35,plain,
    ( spl2_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f50,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f59,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f56,plain,
    ( ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f32,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f54,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f53,f41])).

fof(f41,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f53,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f52,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f48,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,
    ( ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f43,f39,f35])).

fof(f43,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f14,f41])).

fof(f14,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f42,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f13,f39,f35])).

fof(f13,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f31])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f21,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f29,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (25771)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.42  % (25771)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f29,f33,f42,f44,f48,f52,f56,f64,f68,f79])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ~spl2_1 | spl2_4 | ~spl2_7 | ~spl2_8),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    $false | (~spl2_1 | spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.20/0.42    inference(subsumption_resolution,[],[f77,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    sK0 != k4_xboole_0(sK0,sK1) | spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl2_4 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,sK1) | (~spl2_1 | ~spl2_7 | ~spl2_8)),
% 0.20/0.42    inference(forward_demodulation,[],[f73,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl2_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | (~spl2_7 | ~spl2_8)),
% 0.20/0.42    inference(superposition,[],[f67,f63])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl2_7 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl2_8 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f66])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f18,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl2_7 | ~spl2_3 | ~spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f59,f50,f35,f61])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl2_3 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl2_6 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 0.20/0.42    inference(resolution,[],[f51,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK1) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f35])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f50])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_5),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    $false | (~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f54,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl2_2 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.20/0.42    inference(forward_demodulation,[],[f53,f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f39])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (spl2_3 | ~spl2_5)),
% 0.20/0.42    inference(resolution,[],[f47,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ~r1_xboole_0(sK0,sK1) | spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f35])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl2_5 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f50])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f19,f17])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f46])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f20,f17])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ~spl2_3 | ~spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f43,f39,f35])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ~r1_xboole_0(sK0,sK1) | ~spl2_4),
% 0.20/0.42    inference(subsumption_resolution,[],[f14,f41])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_3 | spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f13,f39,f35])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f31])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.42    inference(backward_demodulation,[],[f21,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f15,f17])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f27])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (25771)------------------------------
% 0.20/0.42  % (25771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (25771)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (25771)Memory used [KB]: 6140
% 0.20/0.42  % (25771)Time elapsed: 0.006 s
% 0.20/0.42  % (25771)------------------------------
% 0.20/0.42  % (25771)------------------------------
% 0.20/0.42  % (25763)Success in time 0.063 s
%------------------------------------------------------------------------------
