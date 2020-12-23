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
% DateTime   : Thu Dec  3 12:31:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  85 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 170 expanded)
%              Number of equality atoms :   41 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f508,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f64,f70,f80,f414,f465,f500])).

fof(f500,plain,
    ( spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f479,f462,f60])).

fof(f60,plain,
    ( spl2_2
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f462,plain,
    ( spl2_15
  <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f479,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_15 ),
    inference(superposition,[],[f45,f464])).

fof(f464,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f462])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f465,plain,
    ( spl2_15
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f460,f77,f462])).

fof(f77,plain,
    ( spl2_4
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f460,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f429,f36])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f429,plain,
    ( k3_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_4 ),
    inference(superposition,[],[f44,f79])).

fof(f79,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f414,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f399,f56,f77])).

fof(f56,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f399,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f44,f124])).

fof(f124,plain,
    ( ! [X4] : k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK1))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f121,f45])).

fof(f121,plain,
    ( ! [X4] : k4_xboole_0(sK0,k3_xboole_0(sK0,X4)) = k4_xboole_0(sK0,k4_xboole_0(X4,sK1))
    | ~ spl2_1 ),
    inference(superposition,[],[f45,f96])).

fof(f96,plain,
    ( ! [X2] : k3_xboole_0(sK0,k4_xboole_0(X2,sK1)) = k3_xboole_0(sK0,X2)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f92,f81])).

fof(f81,plain,
    ( ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl2_1 ),
    inference(resolution,[],[f57,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f57,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f92,plain,
    ( ! [X2] : k3_xboole_0(sK0,k4_xboole_0(X2,sK1)) = k3_xboole_0(sK0,k2_xboole_0(sK1,X2))
    | ~ spl2_1 ),
    inference(superposition,[],[f81,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f80,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f69,f60,f77])).

fof(f69,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f44,f61])).

fof(f61,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f70,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f67,f60,f56])).

fof(f67,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f39,f61])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f64,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f34,f60,f56])).

fof(f34,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f32,plain,
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

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f63,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f35,f60,f56])).

fof(f35,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (28817)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.45  % (28806)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (28807)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.46  % (28805)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (28815)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.47  % (28814)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (28803)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (28816)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.48  % (28802)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.49  % (28812)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.49  % (28811)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.49  % (28810)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.50  % (28808)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (28813)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.50  % (28809)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.51  % (28804)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.51  % (28819)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.51  % (28818)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.52  % (28813)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f508,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f63,f64,f70,f80,f414,f465,f500])).
% 0.19/0.52  fof(f500,plain,(
% 0.19/0.52    spl2_2 | ~spl2_15),
% 0.19/0.52    inference(avatar_split_clause,[],[f479,f462,f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    spl2_2 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.52  fof(f462,plain,(
% 0.19/0.52    spl2_15 <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.19/0.52  fof(f479,plain,(
% 0.19/0.52    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_15),
% 0.19/0.52    inference(superposition,[],[f45,f464])).
% 0.19/0.52  fof(f464,plain,(
% 0.19/0.52    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl2_15),
% 0.19/0.52    inference(avatar_component_clause,[],[f462])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.19/0.52  fof(f465,plain,(
% 0.19/0.52    spl2_15 | ~spl2_4),
% 0.19/0.52    inference(avatar_split_clause,[],[f460,f77,f462])).
% 0.19/0.52  fof(f77,plain,(
% 0.19/0.52    spl2_4 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.52  fof(f460,plain,(
% 0.19/0.52    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl2_4),
% 0.19/0.52    inference(forward_demodulation,[],[f429,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.52    inference(rectify,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.19/0.52  fof(f429,plain,(
% 0.19/0.52    k3_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl2_4),
% 0.19/0.52    inference(superposition,[],[f44,f79])).
% 0.19/0.52  fof(f79,plain,(
% 0.19/0.52    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) | ~spl2_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f77])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.52  fof(f414,plain,(
% 0.19/0.52    spl2_4 | ~spl2_1),
% 0.19/0.52    inference(avatar_split_clause,[],[f399,f56,f77])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.52  fof(f399,plain,(
% 0.19/0.52    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) | ~spl2_1),
% 0.19/0.52    inference(superposition,[],[f44,f124])).
% 0.19/0.52  fof(f124,plain,(
% 0.19/0.52    ( ! [X4] : (k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK1))) ) | ~spl2_1),
% 0.19/0.52    inference(forward_demodulation,[],[f121,f45])).
% 0.19/0.52  fof(f121,plain,(
% 0.19/0.52    ( ! [X4] : (k4_xboole_0(sK0,k3_xboole_0(sK0,X4)) = k4_xboole_0(sK0,k4_xboole_0(X4,sK1))) ) | ~spl2_1),
% 0.19/0.52    inference(superposition,[],[f45,f96])).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    ( ! [X2] : (k3_xboole_0(sK0,k4_xboole_0(X2,sK1)) = k3_xboole_0(sK0,X2)) ) | ~spl2_1),
% 0.19/0.52    inference(forward_demodulation,[],[f92,f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X0] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | ~spl2_1),
% 0.19/0.52    inference(resolution,[],[f57,f51])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    r1_xboole_0(sK0,sK1) | ~spl2_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f56])).
% 0.19/0.52  fof(f92,plain,(
% 0.19/0.52    ( ! [X2] : (k3_xboole_0(sK0,k4_xboole_0(X2,sK1)) = k3_xboole_0(sK0,k2_xboole_0(sK1,X2))) ) | ~spl2_1),
% 0.19/0.52    inference(superposition,[],[f81,f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.19/0.52  fof(f80,plain,(
% 0.19/0.52    spl2_4 | ~spl2_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f69,f60,f77])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) | ~spl2_2),
% 0.19/0.52    inference(superposition,[],[f44,f61])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 0.19/0.52    inference(avatar_component_clause,[],[f60])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    spl2_1 | ~spl2_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f67,f60,f56])).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    r1_xboole_0(sK0,sK1) | ~spl2_2),
% 0.19/0.52    inference(superposition,[],[f39,f61])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,axiom,(
% 0.19/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    spl2_1 | spl2_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f34,f60,f56])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.19/0.52    inference(nnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.52    inference(ennf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.52    inference(negated_conjecture,[],[f20])).
% 0.19/0.52  fof(f20,conjecture,(
% 0.19/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ~spl2_1 | ~spl2_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f35,f60,f56])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (28813)------------------------------
% 0.19/0.52  % (28813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (28813)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (28813)Memory used [KB]: 10874
% 0.19/0.52  % (28813)Time elapsed: 0.101 s
% 0.19/0.52  % (28813)------------------------------
% 0.19/0.52  % (28813)------------------------------
% 0.19/0.52  % (28801)Success in time 0.17 s
%------------------------------------------------------------------------------
