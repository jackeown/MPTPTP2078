%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 350 expanded)
%              Number of leaves         :   15 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  133 ( 470 expanded)
%              Number of equality atoms :   53 ( 274 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f89,f510])).

fof(f510,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f91,f508])).

fof(f508,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f505,f66])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f62,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f505,plain,
    ( k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f27,f491])).

fof(f491,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f482,f68])).

fof(f68,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f64,f67])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f63,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f49,f23])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f63,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f27,f47])).

fof(f47,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f27,f45])).

fof(f45,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f482,plain,
    ( ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK1,X16)) = k3_xboole_0(sK0,X16)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f464,f344])).

fof(f344,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f339,f66])).

fof(f339,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f247,f286])).

fof(f286,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f157,f273])).

fof(f273,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f246,f154])).

fof(f154,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3)) = X3 ),
    inference(forward_demodulation,[],[f151,f47])).

fof(f151,plain,(
    ! [X3] : k3_xboole_0(X3,X3) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3)) ),
    inference(superposition,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f246,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f229,f66])).

fof(f229,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f159,f67])).

fof(f159,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f32,f67])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f157,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f156,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f54,f29])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f51,f23])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f25,f26])).

fof(f156,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) ),
    inference(superposition,[],[f28,f154])).

fof(f247,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f159,f246])).

fof(f464,plain,
    ( ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK1,X16)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X16))
    | ~ spl3_1 ),
    inference(superposition,[],[f33,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f93,f67])).

fof(f93,plain,
    ( k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f27,f90])).

fof(f90,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f37,f29])).

fof(f37,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f91,plain,
    ( sK0 != k4_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f42,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f89,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f21,f82])).

fof(f82,plain,
    ( ! [X2] : ~ r1_tarski(sK0,k4_xboole_0(sK1,X2))
    | spl3_1 ),
    inference(resolution,[],[f78,f25])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK0,X0) )
    | spl3_1 ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f43,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f40,f36])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:06:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (15257)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.48  % (15261)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (15266)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.48  % (15265)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.49  % (15262)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.49  % (15271)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.49  % (15260)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.50  % (15263)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.50  % (15269)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.50  % (15256)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.50  % (15272)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.50  % (15259)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.51  % (15267)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.51  % (15258)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.51  % (15264)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.52  % (15270)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.52  % (15272)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f511,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(avatar_sat_refutation,[],[f43,f89,f510])).
% 0.23/0.52  fof(f510,plain,(
% 0.23/0.52    ~spl3_1 | spl3_2),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f509])).
% 0.23/0.52  fof(f509,plain,(
% 0.23/0.52    $false | (~spl3_1 | spl3_2)),
% 0.23/0.52    inference(subsumption_resolution,[],[f91,f508])).
% 0.23/0.52  fof(f508,plain,(
% 0.23/0.52    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_1),
% 0.23/0.52    inference(forward_demodulation,[],[f505,f66])).
% 0.23/0.52  fof(f66,plain,(
% 0.23/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.52    inference(forward_demodulation,[],[f62,f24])).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.52    inference(cnf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.52  fof(f62,plain,(
% 0.23/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.52    inference(superposition,[],[f27,f23])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.52  fof(f505,plain,(
% 0.23/0.52    k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k1_xboole_0) | ~spl3_1),
% 0.23/0.52    inference(superposition,[],[f27,f491])).
% 0.23/0.52  fof(f491,plain,(
% 0.23/0.52    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_1),
% 0.23/0.52    inference(superposition,[],[f482,f68])).
% 0.23/0.52  fof(f68,plain,(
% 0.23/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.52    inference(forward_demodulation,[],[f64,f67])).
% 0.23/0.52  fof(f67,plain,(
% 0.23/0.52    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.23/0.52    inference(forward_demodulation,[],[f63,f52])).
% 0.23/0.52  fof(f52,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.52    inference(forward_demodulation,[],[f49,f23])).
% 0.23/0.52  fof(f49,plain,(
% 0.23/0.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.23/0.52    inference(superposition,[],[f26,f24])).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.52  fof(f63,plain,(
% 0.23/0.52    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.23/0.52    inference(superposition,[],[f27,f47])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 0.23/0.52    inference(resolution,[],[f29,f44])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.23/0.52    inference(superposition,[],[f25,f24])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.52    inference(cnf_transformation,[],[f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.52  fof(f64,plain,(
% 0.23/0.52    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)),
% 0.23/0.52    inference(superposition,[],[f27,f45])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.52    inference(resolution,[],[f29,f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.52    inference(cnf_transformation,[],[f19])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.23/0.52    inference(ennf_transformation,[],[f13])).
% 0.23/0.52  fof(f13,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.23/0.52    inference(negated_conjecture,[],[f12])).
% 0.23/0.52  fof(f12,conjecture,(
% 0.23/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.23/0.52  fof(f482,plain,(
% 0.23/0.52    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X16)) = k3_xboole_0(sK0,X16)) ) | ~spl3_1),
% 0.23/0.52    inference(forward_demodulation,[],[f464,f344])).
% 0.23/0.52  fof(f344,plain,(
% 0.23/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.23/0.52    inference(forward_demodulation,[],[f339,f66])).
% 0.23/0.52  fof(f339,plain,(
% 0.23/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.52    inference(superposition,[],[f247,f286])).
% 0.23/0.52  fof(f286,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) )),
% 0.23/0.52    inference(backward_demodulation,[],[f157,f273])).
% 0.23/0.52  fof(f273,plain,(
% 0.23/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.23/0.52    inference(superposition,[],[f246,f154])).
% 0.23/0.52  fof(f154,plain,(
% 0.23/0.52    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3)) = X3) )),
% 0.23/0.52    inference(forward_demodulation,[],[f151,f47])).
% 0.23/0.52  fof(f151,plain,(
% 0.23/0.52    ( ! [X3] : (k3_xboole_0(X3,X3) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3))) )),
% 0.23/0.52    inference(superposition,[],[f28,f67])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,axiom,(
% 0.23/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.23/0.52  fof(f246,plain,(
% 0.23/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.23/0.52    inference(forward_demodulation,[],[f229,f66])).
% 0.23/0.52  fof(f229,plain,(
% 0.23/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.52    inference(superposition,[],[f159,f67])).
% 0.23/0.52  fof(f159,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.23/0.52    inference(superposition,[],[f32,f67])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  fof(f10,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.23/0.52  fof(f157,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)))) )),
% 0.23/0.52    inference(forward_demodulation,[],[f156,f57])).
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.52    inference(resolution,[],[f54,f29])).
% 0.23/0.52  fof(f54,plain,(
% 0.23/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.52    inference(superposition,[],[f51,f23])).
% 0.23/0.52  fof(f51,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.52    inference(superposition,[],[f25,f26])).
% 0.23/0.52  fof(f156,plain,(
% 0.23/0.52    ( ! [X0] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)))) )),
% 0.23/0.52    inference(superposition,[],[f28,f154])).
% 0.23/0.52  fof(f247,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.23/0.52    inference(backward_demodulation,[],[f159,f246])).
% 0.23/0.52  fof(f464,plain,(
% 0.23/0.52    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X16)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X16))) ) | ~spl3_1),
% 0.23/0.52    inference(superposition,[],[f33,f95])).
% 0.23/0.52  fof(f95,plain,(
% 0.23/0.52    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.23/0.52    inference(forward_demodulation,[],[f93,f67])).
% 0.23/0.52  fof(f93,plain,(
% 0.23/0.52    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.23/0.52    inference(superposition,[],[f27,f90])).
% 0.23/0.52  fof(f90,plain,(
% 0.23/0.52    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_1),
% 0.23/0.52    inference(resolution,[],[f37,f29])).
% 0.23/0.52  fof(f37,plain,(
% 0.23/0.52    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f36])).
% 0.23/0.52  fof(f36,plain,(
% 0.23/0.52    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f8])).
% 0.23/0.52  fof(f8,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.23/0.52  fof(f91,plain,(
% 0.23/0.52    sK0 != k4_xboole_0(sK0,sK2) | spl3_2),
% 0.23/0.52    inference(resolution,[],[f42,f31])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.23/0.52    inference(cnf_transformation,[],[f20])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.23/0.52    inference(nnf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,axiom,(
% 0.23/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.23/0.52    inference(avatar_component_clause,[],[f40])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.52  fof(f89,plain,(
% 0.23/0.52    spl3_1),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f88])).
% 0.23/0.52  fof(f88,plain,(
% 0.23/0.52    $false | spl3_1),
% 0.23/0.52    inference(subsumption_resolution,[],[f21,f82])).
% 0.23/0.52  fof(f82,plain,(
% 0.23/0.52    ( ! [X2] : (~r1_tarski(sK0,k4_xboole_0(sK1,X2))) ) | spl3_1),
% 0.23/0.52    inference(resolution,[],[f78,f25])).
% 0.23/0.52  fof(f78,plain,(
% 0.23/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0)) ) | spl3_1),
% 0.23/0.52    inference(resolution,[],[f34,f38])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f36])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f17])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(flattening,[],[f16])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.52    inference(ennf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    ~spl3_1 | ~spl3_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f22,f40,f36])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f19])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (15272)------------------------------
% 0.23/0.52  % (15272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (15272)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (15272)Memory used [KB]: 6396
% 0.23/0.52  % (15272)Time elapsed: 0.091 s
% 0.23/0.52  % (15272)------------------------------
% 0.23/0.52  % (15272)------------------------------
% 0.23/0.53  % (15255)Success in time 0.155 s
%------------------------------------------------------------------------------
