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
% DateTime   : Thu Dec  3 12:31:33 EST 2020

% Result     : Theorem 3.69s
% Output     : Refutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 164 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  101 ( 283 expanded)
%              Number of equality atoms :   36 (  91 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10415,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10413,f22])).

fof(f22,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f10413,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f10325,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f10325,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f10262,f8473])).

fof(f8473,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
      | r1_xboole_0(X1,sK1) ) ),
    inference(backward_demodulation,[],[f291,f8453])).

fof(f8453,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f8271,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f8271,plain,(
    k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f370,f175])).

fof(f175,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) ),
    inference(superposition,[],[f86,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f86,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f81,f33])).

fof(f81,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f28,f21])).

fof(f21,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f370,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(X8,X9)) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9))))) ),
    inference(forward_demodulation,[],[f346,f33])).

fof(f346,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(X8,X9)) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9)))) ),
    inference(superposition,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f291,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,sK1)
      | ~ r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))) ) ),
    inference(resolution,[],[f266,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f266,plain,(
    ! [X3] : r1_xboole_0(k4_xboole_0(X3,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))),sK1) ),
    inference(resolution,[],[f228,f28])).

fof(f228,plain,(
    ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))) ),
    inference(resolution,[],[f224,f55])).

fof(f55,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | r1_xboole_0(X2,k4_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f224,plain,(
    r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) ),
    inference(trivial_inequality_removal,[],[f221])).

fof(f221,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) ),
    inference(superposition,[],[f31,f175])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f10262,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(sK0,X1),k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) ),
    inference(trivial_inequality_removal,[],[f10251])).

fof(f10251,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,X1),k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) ) ),
    inference(superposition,[],[f31,f481])).

fof(f481,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f472,f33])).

fof(f472,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f450,f37])).

fof(f450,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f66,f420])).

fof(f420,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f33,f379])).

fof(f379,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f355,f23])).

fof(f355,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f35,f82])).

fof(f82,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f37,f21])).

fof(f66,plain,(
    ! [X6,X4,X5] : r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),X5) ),
    inference(resolution,[],[f63,f28])).

fof(f63,plain,(
    ! [X2,X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X1,k2_xboole_0(X1,X2)) ) ),
    inference(superposition,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.41  % (17346)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.42  % (17339)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.44  % (17347)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.44  % (17344)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.45  % (17340)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.45  % (17349)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.45  % (17352)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.45  % (17342)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.45  % (17336)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.46  % (17338)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.46  % (17353)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.46  % (17337)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.47  % (17345)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.47  % (17348)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.47  % (17343)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.48  % (17351)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.50  % (17341)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.51  % (17350)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 3.69/0.87  % (17349)Refutation found. Thanks to Tanya!
% 3.69/0.87  % SZS status Theorem for theBenchmark
% 3.69/0.87  % SZS output start Proof for theBenchmark
% 3.69/0.87  fof(f10415,plain,(
% 3.69/0.87    $false),
% 3.69/0.87    inference(subsumption_resolution,[],[f10413,f22])).
% 3.69/0.87  fof(f22,plain,(
% 3.69/0.87    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 3.69/0.87    inference(cnf_transformation,[],[f18])).
% 3.69/0.87  fof(f18,plain,(
% 3.69/0.87    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.69/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17])).
% 3.69/0.87  fof(f17,plain,(
% 3.69/0.87    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 3.69/0.87    introduced(choice_axiom,[])).
% 3.69/0.87  fof(f13,plain,(
% 3.69/0.87    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 3.69/0.87    inference(ennf_transformation,[],[f12])).
% 3.69/0.87  fof(f12,negated_conjecture,(
% 3.69/0.87    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 3.69/0.87    inference(negated_conjecture,[],[f11])).
% 3.69/0.87  fof(f11,conjecture,(
% 3.69/0.87    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 3.69/0.87  fof(f10413,plain,(
% 3.69/0.87    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 3.69/0.87    inference(resolution,[],[f10325,f28])).
% 3.69/0.87  fof(f28,plain,(
% 3.69/0.87    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.69/0.87    inference(cnf_transformation,[],[f14])).
% 3.69/0.87  fof(f14,plain,(
% 3.69/0.87    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.69/0.87    inference(ennf_transformation,[],[f2])).
% 3.69/0.87  fof(f2,axiom,(
% 3.69/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.69/0.87  fof(f10325,plain,(
% 3.69/0.87    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 3.69/0.87    inference(resolution,[],[f10262,f8473])).
% 3.69/0.87  fof(f8473,plain,(
% 3.69/0.87    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | r1_xboole_0(X1,sK1)) )),
% 3.69/0.87    inference(backward_demodulation,[],[f291,f8453])).
% 3.69/0.87  fof(f8453,plain,(
% 3.69/0.87    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 3.69/0.87    inference(forward_demodulation,[],[f8271,f23])).
% 3.69/0.87  fof(f23,plain,(
% 3.69/0.87    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.69/0.87    inference(cnf_transformation,[],[f4])).
% 3.69/0.87  fof(f4,axiom,(
% 3.69/0.87    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.69/0.87  fof(f8271,plain,(
% 3.69/0.87    k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 3.69/0.87    inference(superposition,[],[f370,f175])).
% 3.69/0.87  fof(f175,plain,(
% 3.69/0.87    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))),
% 3.69/0.87    inference(superposition,[],[f86,f33])).
% 3.69/0.87  fof(f33,plain,(
% 3.69/0.87    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.69/0.87    inference(cnf_transformation,[],[f5])).
% 3.69/0.87  fof(f5,axiom,(
% 3.69/0.87    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.69/0.87  fof(f86,plain,(
% 3.69/0.87    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))),
% 3.69/0.87    inference(forward_demodulation,[],[f81,f33])).
% 3.69/0.87  fof(f81,plain,(
% 3.69/0.87    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0))),
% 3.69/0.87    inference(resolution,[],[f37,f39])).
% 3.69/0.87  fof(f39,plain,(
% 3.69/0.87    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 3.69/0.87    inference(resolution,[],[f28,f21])).
% 3.69/0.87  fof(f21,plain,(
% 3.69/0.87    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.69/0.87    inference(cnf_transformation,[],[f18])).
% 3.69/0.87  fof(f37,plain,(
% 3.69/0.87    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.69/0.87    inference(definition_unfolding,[],[f29,f26])).
% 3.69/0.87  fof(f26,plain,(
% 3.69/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.69/0.87    inference(cnf_transformation,[],[f8])).
% 3.69/0.87  fof(f8,axiom,(
% 3.69/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.69/0.87  fof(f29,plain,(
% 3.69/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.69/0.87    inference(cnf_transformation,[],[f19])).
% 3.69/0.87  fof(f19,plain,(
% 3.69/0.87    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.69/0.87    inference(nnf_transformation,[],[f1])).
% 3.69/0.87  fof(f1,axiom,(
% 3.69/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.69/0.87  fof(f370,plain,(
% 3.69/0.87    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(X8,X9)) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9)))))) )),
% 3.69/0.87    inference(forward_demodulation,[],[f346,f33])).
% 3.69/0.87  fof(f346,plain,(
% 3.69/0.87    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(X8,X9)) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9))))) )),
% 3.69/0.87    inference(superposition,[],[f35,f33])).
% 3.69/0.87  fof(f35,plain,(
% 3.69/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.69/0.87    inference(definition_unfolding,[],[f27,f26])).
% 3.69/0.87  fof(f27,plain,(
% 3.69/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.69/0.87    inference(cnf_transformation,[],[f7])).
% 3.69/0.87  fof(f7,axiom,(
% 3.69/0.87    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.69/0.87  fof(f291,plain,(
% 3.69/0.87    ( ! [X2,X1] : (r1_xboole_0(X1,sK1) | ~r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))))) )),
% 3.69/0.87    inference(resolution,[],[f266,f34])).
% 3.69/0.87  fof(f34,plain,(
% 3.69/0.87    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.69/0.87    inference(cnf_transformation,[],[f16])).
% 3.69/0.87  fof(f16,plain,(
% 3.69/0.87    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.69/0.87    inference(flattening,[],[f15])).
% 3.69/0.87  fof(f15,plain,(
% 3.69/0.87    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.69/0.87    inference(ennf_transformation,[],[f9])).
% 3.69/0.87  fof(f9,axiom,(
% 3.69/0.87    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 3.69/0.87  fof(f266,plain,(
% 3.69/0.87    ( ! [X3] : (r1_xboole_0(k4_xboole_0(X3,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))),sK1)) )),
% 3.69/0.87    inference(resolution,[],[f228,f28])).
% 3.69/0.87  fof(f228,plain,(
% 3.69/0.87    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))))) )),
% 3.69/0.87    inference(resolution,[],[f224,f55])).
% 3.69/0.87  fof(f55,plain,(
% 3.69/0.87    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | r1_xboole_0(X2,k4_xboole_0(X3,X4))) )),
% 3.69/0.87    inference(resolution,[],[f34,f40])).
% 3.69/0.87  fof(f40,plain,(
% 3.69/0.87    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.69/0.87    inference(resolution,[],[f28,f24])).
% 3.69/0.87  fof(f24,plain,(
% 3.69/0.87    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.69/0.87    inference(cnf_transformation,[],[f10])).
% 3.69/0.87  fof(f10,axiom,(
% 3.69/0.87    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.69/0.87  fof(f224,plain,(
% 3.69/0.87    r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))),
% 3.69/0.87    inference(trivial_inequality_removal,[],[f221])).
% 3.69/0.87  fof(f221,plain,(
% 3.69/0.87    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))),
% 3.69/0.87    inference(superposition,[],[f31,f175])).
% 3.69/0.87  fof(f31,plain,(
% 3.69/0.87    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 3.69/0.87    inference(cnf_transformation,[],[f20])).
% 3.69/0.87  fof(f20,plain,(
% 3.69/0.87    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.69/0.87    inference(nnf_transformation,[],[f3])).
% 3.69/0.87  fof(f3,axiom,(
% 3.69/0.87    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.69/0.87  fof(f10262,plain,(
% 3.69/0.87    ( ! [X1] : (r1_tarski(k4_xboole_0(sK0,X1),k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2))))) )),
% 3.69/0.87    inference(trivial_inequality_removal,[],[f10251])).
% 3.69/0.87  fof(f10251,plain,(
% 3.69/0.87    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,X1),k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2))))) )),
% 3.69/0.87    inference(superposition,[],[f31,f481])).
% 3.69/0.87  fof(f481,plain,(
% 3.69/0.87    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))))) )),
% 3.69/0.87    inference(forward_demodulation,[],[f472,f33])).
% 3.69/0.87  fof(f472,plain,(
% 3.69/0.87    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)))) )),
% 3.69/0.87    inference(resolution,[],[f450,f37])).
% 3.69/0.87  fof(f450,plain,(
% 3.69/0.87    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2))) )),
% 3.69/0.87    inference(superposition,[],[f66,f420])).
% 3.69/0.87  fof(f420,plain,(
% 3.69/0.87    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) )),
% 3.69/0.87    inference(superposition,[],[f33,f379])).
% 3.69/0.87  fof(f379,plain,(
% 3.69/0.87    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.69/0.87    inference(forward_demodulation,[],[f355,f23])).
% 3.69/0.87  fof(f355,plain,(
% 3.69/0.87    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 3.69/0.87    inference(superposition,[],[f35,f82])).
% 3.69/0.87  fof(f82,plain,(
% 3.69/0.87    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 3.69/0.87    inference(resolution,[],[f37,f21])).
% 3.69/0.87  fof(f66,plain,(
% 3.69/0.87    ( ! [X6,X4,X5] : (r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),X5)) )),
% 3.69/0.87    inference(resolution,[],[f63,f28])).
% 3.69/0.87  fof(f63,plain,(
% 3.69/0.87    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 3.69/0.87    inference(resolution,[],[f55,f50])).
% 3.69/0.87  fof(f50,plain,(
% 3.69/0.87    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X1,X2))) )),
% 3.69/0.87    inference(trivial_inequality_removal,[],[f49])).
% 3.69/0.87  fof(f49,plain,(
% 3.69/0.87    ( ! [X2,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X1,k2_xboole_0(X1,X2))) )),
% 3.69/0.87    inference(superposition,[],[f31,f25])).
% 3.69/0.87  fof(f25,plain,(
% 3.69/0.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.69/0.87    inference(cnf_transformation,[],[f6])).
% 3.69/0.87  fof(f6,axiom,(
% 3.69/0.87    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.69/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.69/0.87  % SZS output end Proof for theBenchmark
% 3.69/0.87  % (17349)------------------------------
% 3.69/0.87  % (17349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.87  % (17349)Termination reason: Refutation
% 3.69/0.87  
% 3.69/0.87  % (17349)Memory used [KB]: 6908
% 3.69/0.87  % (17349)Time elapsed: 0.459 s
% 3.69/0.87  % (17349)------------------------------
% 3.69/0.87  % (17349)------------------------------
% 3.69/0.88  % (17335)Success in time 0.506 s
%------------------------------------------------------------------------------
