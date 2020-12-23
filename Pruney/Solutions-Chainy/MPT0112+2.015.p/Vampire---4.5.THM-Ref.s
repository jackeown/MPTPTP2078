%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 130 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f35,f49,f64])).

fof(f64,plain,
    ( ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f52,f19])).

fof(f19,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f52,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f28,f45])).

fof(f45,plain,
    ( sK0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f28,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f49,plain,
    ( spl2_4
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f48,f32,f21,f43])).

fof(f21,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f48,plain,
    ( sK0 = sK1
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f47,f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f47,plain,
    ( sK1 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f39,f34])).

fof(f34,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f39,plain,
    ( sK1 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f15,f23])).

fof(f23,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f35,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f30,f26,f32])).

fof(f30,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f28,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f26])).

fof(f12,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f24,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:46:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (28979)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (28972)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (28979)Refutation not found, incomplete strategy% (28979)------------------------------
% 0.21/0.48  % (28979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28979)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28979)Memory used [KB]: 10490
% 0.21/0.48  % (28979)Time elapsed: 0.073 s
% 0.21/0.48  % (28979)------------------------------
% 0.21/0.48  % (28979)------------------------------
% 0.21/0.48  % (28972)Refutation not found, incomplete strategy% (28972)------------------------------
% 0.21/0.48  % (28972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28972)Memory used [KB]: 1535
% 0.21/0.48  % (28972)Time elapsed: 0.070 s
% 0.21/0.48  % (28972)------------------------------
% 0.21/0.48  % (28972)------------------------------
% 0.21/0.50  % (28975)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (28975)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f24,f29,f35,f49,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~spl2_2 | ~spl2_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    $false | (~spl2_2 | ~spl2_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f52,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    r2_xboole_0(sK0,sK0) | (~spl2_2 | ~spl2_4)),
% 0.21/0.51    inference(backward_demodulation,[],[f28,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    sK0 = sK1 | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl2_4 <=> sK0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    r2_xboole_0(sK0,sK1) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    spl2_2 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    spl2_4 | ~spl2_1 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f32,f21,f43])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    spl2_1 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    spl2_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    sK0 = sK1 | (~spl2_1 | ~spl2_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f47,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK0,k1_xboole_0) | (~spl2_1 | ~spl2_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f39,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f32])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(sK0,sK1) | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f15,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f21])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    spl2_3 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f26,f32])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | ~spl2_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f28,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f12,f26])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    r2_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1)) => (k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f13,f21])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28975)------------------------------
% 0.21/0.51  % (28975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28975)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28975)Memory used [KB]: 10618
% 0.21/0.51  % (28975)Time elapsed: 0.086 s
% 0.21/0.51  % (28975)------------------------------
% 0.21/0.51  % (28975)------------------------------
% 0.21/0.51  % (28958)Success in time 0.15 s
%------------------------------------------------------------------------------
