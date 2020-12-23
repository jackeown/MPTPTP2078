%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  79 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  145 ( 270 expanded)
%              Number of equality atoms :   61 ( 129 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f43,f46,f60,f67,f72])).

fof(f72,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f70,f26])).

fof(f26,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f70,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f30,f33])).

fof(f33,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,k1_tarski(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> r1_tarski(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f67,plain,
    ( spl2_1
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f62,f23])).

fof(f23,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f62,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl2_1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f30,f42])).

fof(f42,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( ~ spl2_1
    | spl2_2
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | spl2_3 ),
    inference(subsumption_resolution,[],[f58,f41])).

fof(f41,plain,
    ( sK0 != k1_tarski(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f58,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f56,f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK0
    | spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f56,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,
    ( r1_tarski(sK0,k1_tarski(sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,
    ( ~ spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f45,f28,f40])).

fof(f45,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f16,f29])).

fof(f16,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( ( sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k1_tarski(sK1)) )
    & ( sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ( ( k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k1_tarski(X1)) )
        & ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k1_tarski(X1)) ) )
   => ( ( ( sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k1_tarski(sK1)) )
      & ( sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f43,plain,
    ( spl2_2
    | spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f38,f28,f40,f32])).

fof(f38,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | spl2_1 ),
    inference(subsumption_resolution,[],[f14,f30])).

fof(f14,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f32,f28])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:01:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (6555)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (6548)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (6548)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f35,f43,f46,f60,f67,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl2_1 | ~spl2_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    $false | (spl2_1 | ~spl2_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f70,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,k1_tarski(sK1)) | (spl2_1 | ~spl2_2)),
% 0.22/0.50    inference(forward_demodulation,[],[f30,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    spl2_2 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~r1_tarski(sK0,k1_tarski(sK1)) | spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    spl2_1 <=> r1_tarski(sK0,k1_tarski(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl2_1 | ~spl2_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    $false | (spl2_1 | ~spl2_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f62,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK0) | (spl2_1 | ~spl2_3)),
% 0.22/0.50    inference(backward_demodulation,[],[f30,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    sK0 = k1_tarski(sK1) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    spl2_3 <=> sK0 = k1_tarski(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ~spl2_1 | spl2_2 | spl2_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    $false | (~spl2_1 | spl2_2 | spl2_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f58,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    sK0 != k1_tarski(sK1) | spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f40])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    sK0 = k1_tarski(sK1) | (~spl2_1 | spl2_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f56,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    k1_xboole_0 != sK0 | spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f32])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | ~spl2_1),
% 0.22/0.50    inference(resolution,[],[f20,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    r1_tarski(sK0,k1_tarski(sK1)) | ~spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f28])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ~spl2_3 | ~spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f28,f40])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    sK0 != k1_tarski(sK1) | ~spl2_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f16,f29])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1)))) => (((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,plain,(
% 0.22/0.50    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.50    inference(negated_conjecture,[],[f3])).
% 0.22/0.50  fof(f3,conjecture,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl2_2 | spl2_3 | spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f28,f40,f32])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | spl2_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f14,f30])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ~spl2_1 | ~spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f15,f32,f28])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (6548)------------------------------
% 0.22/0.50  % (6548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6548)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (6548)Memory used [KB]: 6140
% 0.22/0.50  % (6548)Time elapsed: 0.094 s
% 0.22/0.50  % (6548)------------------------------
% 0.22/0.50  % (6548)------------------------------
% 0.22/0.50  % (6562)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.50  % (6545)Success in time 0.143 s
%------------------------------------------------------------------------------
