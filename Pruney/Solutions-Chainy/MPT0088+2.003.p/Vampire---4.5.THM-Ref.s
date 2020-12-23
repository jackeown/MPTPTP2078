%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  80 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 136 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f120,f151,f402])).

fof(f402,plain,
    ( spl3_3
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f379,f165])).

fof(f165,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f156,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f156,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | ~ spl3_6 ),
    inference(superposition,[],[f150,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f32,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f150,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f379,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f119,f304])).

fof(f304,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X4)))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(backward_demodulation,[],[f76,f291])).

fof(f291,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f69,f21])).

fof(f69,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f22,f28])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f76,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4))))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(forward_demodulation,[],[f68,f28])).

fof(f68,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(superposition,[],[f30,f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f119,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_3
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f151,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f36,f148])).

fof(f36,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f120,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f45,f41,f117])).

fof(f41,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f43,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f44,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:36:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (28779)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (28780)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (28790)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (28792)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (28793)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (28777)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (28781)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (28784)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (28783)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (28778)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (28786)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (28788)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (28792)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f418,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f39,f44,f120,f151,f402])).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    spl3_3 | ~spl3_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f401])).
% 0.22/0.51  fof(f401,plain,(
% 0.22/0.51    $false | (spl3_3 | ~spl3_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f379,f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_6),
% 0.22/0.51    inference(forward_demodulation,[],[f156,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) | ~spl3_6),
% 0.22/0.51    inference(superposition,[],[f150,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.22/0.51    inference(backward_demodulation,[],[f32,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f27,f23,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f148])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f379,plain,(
% 0.22/0.51    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | spl3_3),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f119,f304])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X4))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f76,f291])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 0.22/0.51    inference(superposition,[],[f69,f21])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 0.22/0.51    inference(superposition,[],[f22,f28])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f68,f28])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 0.22/0.51    inference(superposition,[],[f30,f28])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f26,f23])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl3_3 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    spl3_6 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f36,f148])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_1),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f38,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f25,f23])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f36])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ~spl3_3 | spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f41,f117])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    spl3_2 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f43,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f41])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f41])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28792)------------------------------
% 0.22/0.51  % (28792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28792)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28792)Memory used [KB]: 11001
% 0.22/0.51  % (28792)Time elapsed: 0.036 s
% 0.22/0.51  % (28792)------------------------------
% 0.22/0.51  % (28792)------------------------------
% 0.22/0.52  % (28787)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (28776)Success in time 0.156 s
%------------------------------------------------------------------------------
