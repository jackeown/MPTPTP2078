%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:36 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 410 expanded)
%              Number of leaves         :   11 ( 136 expanded)
%              Depth                    :   23
%              Number of atoms          :  136 ( 588 expanded)
%              Number of equality atoms :   61 ( 374 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1875,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f37,f41,f1874])).

fof(f1874,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1870])).

fof(f1870,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(resolution,[],[f1743,f30])).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1743,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_2 ),
    inference(resolution,[],[f1719,f365])).

fof(f365,plain,(
    ! [X8,X9] :
      ( r1_xboole_0(X8,X9)
      | ~ r1_xboole_0(X9,X8) ) ),
    inference(trivial_inequality_removal,[],[f349])).

fof(f349,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X8,X9)
      | ~ r1_xboole_0(X9,X8) ) ),
    inference(superposition,[],[f26,f90])).

fof(f90,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X4))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f25,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f20,f20])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1719,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f1718])).

fof(f1718,plain,
    ( sK0 != sK0
    | ~ r1_xboole_0(sK1,sK0)
    | spl2_2 ),
    inference(superposition,[],[f35,f1378])).

fof(f1378,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,X5) = X4
      | ~ r1_xboole_0(X5,X4) ) ),
    inference(forward_demodulation,[],[f1377,f606])).

fof(f606,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = X4 ),
    inference(forward_demodulation,[],[f605,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f605,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f604,f473])).

fof(f473,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f88,f443])).

fof(f443,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f397,f317])).

fof(f317,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f18,f17])).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f51,f17])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f27,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f27,f17])).

fof(f397,plain,(
    ! [X2,X3] : r1_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f81,f61])).

fof(f61,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f81,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f68,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f68,plain,(
    ! [X12,X13,X11] : r1_xboole_0(k4_xboole_0(X11,k2_xboole_0(X12,X13)),X13) ),
    inference(superposition,[],[f18,f24])).

fof(f88,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f25,f17])).

fof(f604,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,X4)) ),
    inference(forward_demodulation,[],[f603,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f24,f17])).

fof(f603,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(k1_xboole_0,X4))) ),
    inference(forward_demodulation,[],[f582,f17])).

fof(f582,plain,(
    ! [X4] : k4_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(k1_xboole_0,X4))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(superposition,[],[f25,f516])).

fof(f516,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(superposition,[],[f473,f57])).

fof(f1377,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,X5) = k2_xboole_0(k1_xboole_0,X4)
      | ~ r1_xboole_0(X5,X4) ) ),
    inference(forward_demodulation,[],[f1376,f606])).

fof(f1376,plain,(
    ! [X4,X5] :
      ( k2_xboole_0(k1_xboole_0,X4) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5))
      | ~ r1_xboole_0(X5,X4) ) ),
    inference(forward_demodulation,[],[f1375,f537])).

fof(f537,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f518,f21])).

fof(f518,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f473,f24])).

fof(f1375,plain,(
    ! [X4,X5] :
      ( k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X4)
      | ~ r1_xboole_0(X5,X4) ) ),
    inference(forward_demodulation,[],[f1374,f24])).

fof(f1374,plain,(
    ! [X4,X5] :
      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),X4)
      | ~ r1_xboole_0(X5,X4) ) ),
    inference(forward_demodulation,[],[f1319,f17])).

fof(f1319,plain,(
    ! [X4,X5] :
      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),k4_xboole_0(X4,k1_xboole_0))
      | ~ r1_xboole_0(X5,X4) ) ),
    inference(superposition,[],[f99,f90])).

fof(f99,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))) ),
    inference(superposition,[],[f21,f25])).

fof(f35,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_2
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f38,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f18,f34])).

fof(f34,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f37,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f15,f33,f29])).

fof(f15,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
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

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f36,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f16,f33,f29])).

fof(f16,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (12886)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.46  % (12879)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (12885)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (12892)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (12884)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (12878)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (12883)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (12887)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (12891)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (12890)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (12882)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (12888)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (12880)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (12894)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (12893)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (12895)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (12889)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (12881)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (12889)Refutation not found, incomplete strategy% (12889)------------------------------
% 0.22/0.51  % (12889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12889)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12889)Memory used [KB]: 10618
% 0.22/0.51  % (12889)Time elapsed: 0.096 s
% 0.22/0.51  % (12889)------------------------------
% 0.22/0.51  % (12889)------------------------------
% 1.56/0.56  % (12882)Refutation found. Thanks to Tanya!
% 1.56/0.56  % SZS status Theorem for theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f1875,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(avatar_sat_refutation,[],[f36,f37,f41,f1874])).
% 1.56/0.56  fof(f1874,plain,(
% 1.56/0.56    ~spl2_1 | spl2_2),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f1870])).
% 1.56/0.56  fof(f1870,plain,(
% 1.56/0.56    $false | (~spl2_1 | spl2_2)),
% 1.56/0.56    inference(resolution,[],[f1743,f30])).
% 1.56/0.56  fof(f30,plain,(
% 1.56/0.56    r1_xboole_0(sK0,sK1) | ~spl2_1),
% 1.56/0.56    inference(avatar_component_clause,[],[f29])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.56/0.56  fof(f1743,plain,(
% 1.56/0.56    ~r1_xboole_0(sK0,sK1) | spl2_2),
% 1.56/0.56    inference(resolution,[],[f1719,f365])).
% 1.56/0.56  fof(f365,plain,(
% 1.56/0.56    ( ! [X8,X9] : (r1_xboole_0(X8,X9) | ~r1_xboole_0(X9,X8)) )),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f349])).
% 1.56/0.56  fof(f349,plain,(
% 1.56/0.56    ( ! [X8,X9] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X8,X9) | ~r1_xboole_0(X9,X8)) )),
% 1.56/0.56    inference(superposition,[],[f26,f90])).
% 1.56/0.56  fof(f90,plain,(
% 1.56/0.56    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X4)) | ~r1_xboole_0(X4,X5)) )),
% 1.56/0.56    inference(superposition,[],[f25,f27])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.56/0.56    inference(definition_unfolding,[],[f22,f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,axiom,(
% 1.56/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f14])).
% 1.56/0.56  fof(f14,plain,(
% 1.56/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.56/0.56    inference(nnf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.56/0.56    inference(definition_unfolding,[],[f19,f20,f20])).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f1])).
% 1.56/0.56  fof(f1,axiom,(
% 1.56/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.56/0.56    inference(definition_unfolding,[],[f23,f20])).
% 1.56/0.56  fof(f23,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f14])).
% 1.56/0.56  fof(f1719,plain,(
% 1.56/0.56    ~r1_xboole_0(sK1,sK0) | spl2_2),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f1718])).
% 1.56/0.56  fof(f1718,plain,(
% 1.56/0.56    sK0 != sK0 | ~r1_xboole_0(sK1,sK0) | spl2_2),
% 1.56/0.56    inference(superposition,[],[f35,f1378])).
% 1.56/0.56  fof(f1378,plain,(
% 1.56/0.56    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = X4 | ~r1_xboole_0(X5,X4)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f1377,f606])).
% 1.56/0.56  fof(f606,plain,(
% 1.56/0.56    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = X4) )),
% 1.56/0.56    inference(forward_demodulation,[],[f605,f17])).
% 1.56/0.56  fof(f17,plain,(
% 1.56/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.56/0.56  fof(f605,plain,(
% 1.56/0.56    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k1_xboole_0)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f604,f473])).
% 1.56/0.56  fof(f473,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.56/0.56    inference(backward_demodulation,[],[f88,f443])).
% 1.56/0.56  fof(f443,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.56/0.56    inference(resolution,[],[f397,f317])).
% 1.56/0.56  fof(f317,plain,(
% 1.56/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(resolution,[],[f55,f39])).
% 1.56/0.56  fof(f39,plain,(
% 1.56/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.56/0.56    inference(superposition,[],[f18,f17])).
% 1.56/0.56  fof(f18,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,axiom,(
% 1.56/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.56/0.56  fof(f55,plain,(
% 1.56/0.56    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(forward_demodulation,[],[f51,f17])).
% 1.56/0.56  fof(f51,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.56/0.56    inference(superposition,[],[f27,f43])).
% 1.56/0.56  fof(f43,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.56/0.56    inference(superposition,[],[f27,f17])).
% 1.56/0.56  fof(f397,plain,(
% 1.56/0.56    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k1_xboole_0,X3))) )),
% 1.56/0.56    inference(superposition,[],[f81,f61])).
% 1.56/0.56  fof(f61,plain,(
% 1.56/0.56    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 1.56/0.56    inference(superposition,[],[f24,f17])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.56/0.56  fof(f81,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) )),
% 1.56/0.56    inference(superposition,[],[f68,f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.56/0.56  fof(f68,plain,(
% 1.56/0.56    ( ! [X12,X13,X11] : (r1_xboole_0(k4_xboole_0(X11,k2_xboole_0(X12,X13)),X13)) )),
% 1.56/0.56    inference(superposition,[],[f18,f24])).
% 1.56/0.56  fof(f88,plain,(
% 1.56/0.56    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.56/0.56    inference(superposition,[],[f25,f17])).
% 1.56/0.56  fof(f604,plain,(
% 1.56/0.56    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,X4))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f603,f57])).
% 1.56/0.56  fof(f57,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 1.56/0.56    inference(superposition,[],[f24,f17])).
% 1.56/0.56  fof(f603,plain,(
% 1.56/0.56    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(k1_xboole_0,X4)))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f582,f17])).
% 1.56/0.56  fof(f582,plain,(
% 1.56/0.56    ( ! [X4] : (k4_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(k1_xboole_0,X4))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 1.56/0.56    inference(superposition,[],[f25,f516])).
% 1.56/0.56  fof(f516,plain,(
% 1.56/0.56    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)) )),
% 1.56/0.56    inference(superposition,[],[f473,f57])).
% 1.56/0.56  fof(f1377,plain,(
% 1.56/0.56    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k2_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(X5,X4)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f1376,f606])).
% 1.56/0.56  fof(f1376,plain,(
% 1.56/0.56    ( ! [X4,X5] : (k2_xboole_0(k1_xboole_0,X4) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) | ~r1_xboole_0(X5,X4)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f1375,f537])).
% 1.56/0.56  fof(f537,plain,(
% 1.56/0.56    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f518,f21])).
% 1.56/0.56  fof(f518,plain,(
% 1.56/0.56    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4)))) )),
% 1.56/0.56    inference(superposition,[],[f473,f24])).
% 1.56/0.56  fof(f1375,plain,(
% 1.56/0.56    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X4) | ~r1_xboole_0(X5,X4)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f1374,f24])).
% 1.56/0.56  fof(f1374,plain,(
% 1.56/0.56    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),X4) | ~r1_xboole_0(X5,X4)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f1319,f17])).
% 1.56/0.56  fof(f1319,plain,(
% 1.56/0.56    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X4),k4_xboole_0(X4,k1_xboole_0)) | ~r1_xboole_0(X5,X4)) )),
% 1.56/0.56    inference(superposition,[],[f99,f90])).
% 1.56/0.56  fof(f99,plain,(
% 1.56/0.56    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6)))) )),
% 1.56/0.56    inference(superposition,[],[f21,f25])).
% 1.56/0.56  fof(f35,plain,(
% 1.56/0.56    sK0 != k4_xboole_0(sK0,sK1) | spl2_2),
% 1.56/0.56    inference(avatar_component_clause,[],[f33])).
% 1.56/0.56  fof(f33,plain,(
% 1.56/0.56    spl2_2 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.56/0.56  fof(f41,plain,(
% 1.56/0.56    spl2_1 | ~spl2_2),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f40])).
% 1.56/0.56  fof(f40,plain,(
% 1.56/0.56    $false | (spl2_1 | ~spl2_2)),
% 1.56/0.56    inference(resolution,[],[f38,f31])).
% 1.56/0.56  fof(f31,plain,(
% 1.56/0.56    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 1.56/0.56    inference(avatar_component_clause,[],[f29])).
% 1.56/0.56  fof(f38,plain,(
% 1.56/0.56    r1_xboole_0(sK0,sK1) | ~spl2_2),
% 1.56/0.56    inference(superposition,[],[f18,f34])).
% 1.56/0.56  fof(f34,plain,(
% 1.56/0.56    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 1.56/0.56    inference(avatar_component_clause,[],[f33])).
% 1.56/0.56  fof(f37,plain,(
% 1.56/0.56    spl2_1 | spl2_2),
% 1.56/0.56    inference(avatar_split_clause,[],[f15,f33,f29])).
% 1.56/0.56  fof(f15,plain,(
% 1.56/0.56    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 1.56/0.56    inference(cnf_transformation,[],[f13])).
% 1.56/0.56  fof(f13,plain,(
% 1.56/0.56    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 1.56/0.56  fof(f12,plain,(
% 1.56/0.56    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f11,plain,(
% 1.56/0.56    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 1.56/0.56    inference(nnf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,plain,(
% 1.56/0.56    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 1.56/0.56    inference(ennf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.56/0.56    inference(negated_conjecture,[],[f8])).
% 1.56/0.56  fof(f8,conjecture,(
% 1.56/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    ~spl2_1 | ~spl2_2),
% 1.56/0.56    inference(avatar_split_clause,[],[f16,f33,f29])).
% 1.56/0.56  fof(f16,plain,(
% 1.56/0.56    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 1.56/0.56    inference(cnf_transformation,[],[f13])).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (12882)------------------------------
% 1.56/0.56  % (12882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (12882)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (12882)Memory used [KB]: 7164
% 1.56/0.56  % (12882)Time elapsed: 0.133 s
% 1.56/0.56  % (12882)------------------------------
% 1.56/0.56  % (12882)------------------------------
% 1.56/0.56  % (12877)Success in time 0.204 s
%------------------------------------------------------------------------------
