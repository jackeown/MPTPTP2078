%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:45 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 161 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :   90 ( 232 expanded)
%              Number of equality atoms :   56 ( 155 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3482,plain,(
    $false ),
    inference(resolution,[],[f3477,f19])).

fof(f19,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
        & r1_xboole_0(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f3477,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f3286,f2361])).

fof(f2361,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f2313])).

fof(f2313,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f43,f145])).

fof(f145,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(k2_xboole_0(X2,X4),X3) = k2_xboole_0(X2,k4_xboole_0(X4,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f33,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f43,plain,(
    k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f42,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f20,f23])).

fof(f20,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f3286,plain,(
    ! [X6,X5] :
      ( r1_xboole_0(X6,X5)
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f3207,f29])).

fof(f3207,plain,(
    ! [X8,X9] : r1_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f22,f3044])).

fof(f3044,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f3043,f652])).

fof(f652,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(superposition,[],[f640,f23])).

fof(f640,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(forward_demodulation,[],[f639,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f639,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f218,f391])).

fof(f391,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f256,f341])).

fof(f341,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f325])).

fof(f325,plain,(
    ! [X10,X9] :
      ( k1_xboole_0 = X9
      | ~ r1_xboole_0(X9,X9)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(superposition,[],[f29,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X1)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X1)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f35,f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f256,plain,(
    ! [X4,X3] : r1_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X3)) ),
    inference(superposition,[],[f112,f197])).

fof(f197,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(forward_demodulation,[],[f186,f66])).

fof(f66,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f59,f21])).

fof(f59,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f186,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f25,f80])).

fof(f80,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f26,f69])).

fof(f69,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f66,f23])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f112,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),X4) ),
    inference(superposition,[],[f22,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f218,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f36,f25])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f3043,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2937,f21])).

fof(f2937,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f219,f391])).

fof(f219,plain,(
    ! [X8,X7,X9] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X9)),k4_xboole_0(X7,X8)) = k4_xboole_0(X7,k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f36,f23])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (11864)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (11878)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (11868)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (11872)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (11862)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (11867)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (11863)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (11865)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (11876)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (11869)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (11866)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (11879)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (11871)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (11874)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (11875)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (11877)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (11873)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (11870)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.88/0.59  % (11866)Refutation found. Thanks to Tanya!
% 1.88/0.59  % SZS status Theorem for theBenchmark
% 1.88/0.59  % SZS output start Proof for theBenchmark
% 1.88/0.59  fof(f3482,plain,(
% 1.88/0.59    $false),
% 1.88/0.59    inference(resolution,[],[f3477,f19])).
% 1.88/0.59  fof(f19,plain,(
% 1.88/0.59    r1_xboole_0(sK0,sK1)),
% 1.88/0.59    inference(cnf_transformation,[],[f16])).
% 1.88/0.59  fof(f16,plain,(
% 1.88/0.59    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1)),
% 1.88/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 1.88/0.59  fof(f15,plain,(
% 1.88/0.59    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1))),
% 1.88/0.59    introduced(choice_axiom,[])).
% 1.88/0.59  fof(f14,plain,(
% 1.88/0.59    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1))),
% 1.88/0.59    inference(ennf_transformation,[],[f13])).
% 1.88/0.61  fof(f13,negated_conjecture,(
% 1.88/0.61    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 1.88/0.61    inference(negated_conjecture,[],[f12])).
% 1.88/0.61  fof(f12,conjecture,(
% 1.88/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 1.88/0.61  fof(f3477,plain,(
% 1.88/0.61    ~r1_xboole_0(sK0,sK1)),
% 1.88/0.61    inference(resolution,[],[f3286,f2361])).
% 1.88/0.61  fof(f2361,plain,(
% 1.88/0.61    ~r1_xboole_0(sK1,sK0)),
% 1.88/0.61    inference(trivial_inequality_removal,[],[f2313])).
% 1.88/0.61  fof(f2313,plain,(
% 1.88/0.61    k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) | ~r1_xboole_0(sK1,sK0)),
% 1.88/0.61    inference(superposition,[],[f43,f145])).
% 1.88/0.61  fof(f145,plain,(
% 1.88/0.61    ( ! [X4,X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X4),X3) = k2_xboole_0(X2,k4_xboole_0(X4,X3)) | ~r1_xboole_0(X2,X3)) )),
% 1.88/0.61    inference(superposition,[],[f33,f29])).
% 1.88/0.61  fof(f29,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f18])).
% 1.88/0.61  fof(f18,plain,(
% 1.88/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.88/0.61    inference(nnf_transformation,[],[f11])).
% 1.88/0.61  fof(f11,axiom,(
% 1.88/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.88/0.61  fof(f33,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f7])).
% 1.88/0.61  fof(f7,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.88/0.61  fof(f43,plain,(
% 1.88/0.61    k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),
% 1.88/0.61    inference(forward_demodulation,[],[f42,f23])).
% 1.88/0.61  fof(f23,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f1])).
% 1.88/0.61  fof(f1,axiom,(
% 1.88/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.88/0.61  fof(f42,plain,(
% 1.88/0.61    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)),
% 1.88/0.61    inference(forward_demodulation,[],[f20,f23])).
% 1.88/0.61  fof(f20,plain,(
% 1.88/0.61    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)),
% 1.88/0.61    inference(cnf_transformation,[],[f16])).
% 1.88/0.61  fof(f3286,plain,(
% 1.88/0.61    ( ! [X6,X5] : (r1_xboole_0(X6,X5) | ~r1_xboole_0(X5,X6)) )),
% 1.88/0.61    inference(superposition,[],[f3207,f29])).
% 1.88/0.61  fof(f3207,plain,(
% 1.88/0.61    ( ! [X8,X9] : (r1_xboole_0(X8,k4_xboole_0(X9,X8))) )),
% 1.88/0.61    inference(superposition,[],[f22,f3044])).
% 1.88/0.61  fof(f3044,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 1.88/0.61    inference(forward_demodulation,[],[f3043,f652])).
% 1.88/0.61  fof(f652,plain,(
% 1.88/0.61    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 1.88/0.61    inference(superposition,[],[f640,f23])).
% 1.88/0.61  fof(f640,plain,(
% 1.88/0.61    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 1.88/0.61    inference(forward_demodulation,[],[f639,f21])).
% 1.88/0.61  fof(f21,plain,(
% 1.88/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.88/0.61    inference(cnf_transformation,[],[f4])).
% 1.88/0.61  fof(f4,axiom,(
% 1.88/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.88/0.61  fof(f639,plain,(
% 1.88/0.61    ( ! [X6,X5] : (k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 1.88/0.61    inference(forward_demodulation,[],[f218,f391])).
% 1.88/0.61  fof(f391,plain,(
% 1.88/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.88/0.61    inference(resolution,[],[f256,f341])).
% 1.88/0.61  fof(f341,plain,(
% 1.88/0.61    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.88/0.61    inference(condensation,[],[f325])).
% 1.88/0.61  fof(f325,plain,(
% 1.88/0.61    ( ! [X10,X9] : (k1_xboole_0 = X9 | ~r1_xboole_0(X9,X9) | ~r1_xboole_0(X9,X10)) )),
% 1.88/0.61    inference(superposition,[],[f29,f97])).
% 1.88/0.61  fof(f97,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X1) | ~r1_xboole_0(X1,X2)) )),
% 1.88/0.61    inference(duplicate_literal_removal,[],[f87])).
% 1.88/0.61  fof(f87,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X1) | ~r1_xboole_0(X1,X2) | ~r1_xboole_0(X1,X2)) )),
% 1.88/0.61    inference(superposition,[],[f35,f29])).
% 1.88/0.61  fof(f35,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(definition_unfolding,[],[f27,f24])).
% 1.88/0.61  fof(f24,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f8])).
% 1.88/0.61  fof(f8,axiom,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.88/0.61  fof(f27,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f17])).
% 1.88/0.61  fof(f17,plain,(
% 1.88/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.88/0.61    inference(nnf_transformation,[],[f2])).
% 1.88/0.61  fof(f2,axiom,(
% 1.88/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.88/0.61  fof(f256,plain,(
% 1.88/0.61    ( ! [X4,X3] : (r1_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X3))) )),
% 1.88/0.61    inference(superposition,[],[f112,f197])).
% 1.88/0.61  fof(f197,plain,(
% 1.88/0.61    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 1.88/0.61    inference(forward_demodulation,[],[f186,f66])).
% 1.88/0.61  fof(f66,plain,(
% 1.88/0.61    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.88/0.61    inference(forward_demodulation,[],[f59,f21])).
% 1.88/0.61  fof(f59,plain,(
% 1.88/0.61    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.88/0.61    inference(superposition,[],[f26,f21])).
% 1.88/0.61  fof(f26,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f5])).
% 1.88/0.61  fof(f5,axiom,(
% 1.88/0.61    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.88/0.61  fof(f186,plain,(
% 1.88/0.61    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X1,X1))) )),
% 1.88/0.61    inference(superposition,[],[f25,f80])).
% 1.88/0.61  fof(f80,plain,(
% 1.88/0.61    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.88/0.61    inference(superposition,[],[f26,f69])).
% 1.88/0.61  fof(f69,plain,(
% 1.88/0.61    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.88/0.61    inference(superposition,[],[f66,f23])).
% 1.88/0.61  fof(f25,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f3])).
% 1.88/0.61  fof(f3,axiom,(
% 1.88/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.88/0.61  fof(f112,plain,(
% 1.88/0.61    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),X4)) )),
% 1.88/0.61    inference(superposition,[],[f22,f31])).
% 1.88/0.61  fof(f31,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f6])).
% 1.88/0.61  fof(f6,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.88/0.61  fof(f218,plain,(
% 1.88/0.61    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6))) )),
% 1.88/0.61    inference(superposition,[],[f36,f25])).
% 1.88/0.61  fof(f36,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f32,f24])).
% 1.88/0.61  fof(f32,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f9])).
% 1.88/0.61  fof(f9,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.88/0.61  fof(f3043,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(forward_demodulation,[],[f2937,f21])).
% 1.88/0.61  fof(f2937,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(superposition,[],[f219,f391])).
% 1.88/0.61  fof(f219,plain,(
% 1.88/0.61    ( ! [X8,X7,X9] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X9)),k4_xboole_0(X7,X8)) = k4_xboole_0(X7,k4_xboole_0(X8,X9))) )),
% 1.88/0.61    inference(superposition,[],[f36,f23])).
% 1.88/0.61  fof(f22,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f10])).
% 1.88/0.61  fof(f10,axiom,(
% 1.88/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.88/0.61  % SZS output end Proof for theBenchmark
% 1.88/0.61  % (11866)------------------------------
% 1.88/0.61  % (11866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (11866)Termination reason: Refutation
% 1.88/0.61  
% 1.88/0.61  % (11866)Memory used [KB]: 8059
% 1.88/0.61  % (11866)Time elapsed: 0.182 s
% 1.88/0.61  % (11866)------------------------------
% 1.88/0.61  % (11866)------------------------------
% 1.88/0.61  % (11861)Success in time 0.252 s
%------------------------------------------------------------------------------
