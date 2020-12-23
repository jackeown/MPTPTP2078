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
% DateTime   : Thu Dec  3 12:31:32 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 122 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :   93 ( 157 expanded)
%              Number of equality atoms :   46 (  98 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3156,plain,(
    $false ),
    inference(resolution,[],[f3078,f28])).

fof(f28,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f3078,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f33,f3055])).

fof(f3055,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2956,f531])).

fof(f531,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f530,f185])).

fof(f185,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(superposition,[],[f168,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f168,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[],[f106,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f106,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8) = X8 ),
    inference(forward_demodulation,[],[f100,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f100,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8) = k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f35,f45])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f530,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f529,f34])).

fof(f529,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f495,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f495,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f44,f31])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f2956,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f532,f556])).

fof(f556,plain,(
    ! [X16] : k4_xboole_0(sK0,X16) = k4_xboole_0(sK0,k4_xboole_0(X16,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f555,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f555,plain,(
    ! [X16] : k4_xboole_0(sK0,k4_xboole_0(X16,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X16),k1_xboole_0) ),
    inference(forward_demodulation,[],[f500,f52])).

fof(f500,plain,(
    ! [X16] : k4_xboole_0(sK0,k4_xboole_0(X16,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X16),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f51,f123])).

fof(f123,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f117,f31])).

fof(f117,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f45,f81])).

fof(f81,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f69,f27])).

fof(f27,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f532,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X4,k4_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f496,f51])).

fof(f496,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X4,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f51,f45])).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 13:09:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (28766)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (28769)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (28761)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (28772)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (28774)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (28762)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (28764)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (28763)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (28770)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (28770)Refutation not found, incomplete strategy% (28770)------------------------------
% 0.22/0.50  % (28770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28773)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (28765)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (28768)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (28771)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (28776)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (28770)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28770)Memory used [KB]: 10618
% 0.22/0.51  % (28770)Time elapsed: 0.069 s
% 0.22/0.51  % (28770)------------------------------
% 0.22/0.51  % (28770)------------------------------
% 0.22/0.51  % (28760)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (28775)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (28759)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.53  % (28767)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 2.02/0.63  % (28760)Refutation found. Thanks to Tanya!
% 2.02/0.63  % SZS status Theorem for theBenchmark
% 2.02/0.63  % SZS output start Proof for theBenchmark
% 2.02/0.63  fof(f3156,plain,(
% 2.02/0.63    $false),
% 2.02/0.63    inference(resolution,[],[f3078,f28])).
% 2.02/0.63  fof(f28,plain,(
% 2.02/0.63    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.02/0.63    inference(cnf_transformation,[],[f22])).
% 2.02/0.63  fof(f22,plain,(
% 2.02/0.63    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 2.02/0.63  fof(f21,plain,(
% 2.02/0.63    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f18,plain,(
% 2.02/0.63    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.02/0.63    inference(ennf_transformation,[],[f16])).
% 2.02/0.63  fof(f16,negated_conjecture,(
% 2.02/0.63    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.02/0.63    inference(negated_conjecture,[],[f15])).
% 2.02/0.63  fof(f15,conjecture,(
% 2.02/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 2.02/0.63  fof(f3078,plain,(
% 2.02/0.63    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.02/0.63    inference(superposition,[],[f33,f3055])).
% 2.02/0.63  fof(f3055,plain,(
% 2.02/0.63    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.02/0.63    inference(forward_demodulation,[],[f2956,f531])).
% 2.02/0.63  fof(f531,plain,(
% 2.02/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 2.02/0.63    inference(forward_demodulation,[],[f530,f185])).
% 2.02/0.63  fof(f185,plain,(
% 2.02/0.63    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 2.02/0.63    inference(superposition,[],[f168,f34])).
% 2.02/0.63  fof(f34,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f1])).
% 2.02/0.63  fof(f1,axiom,(
% 2.02/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.02/0.63  fof(f168,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 2.02/0.63    inference(superposition,[],[f106,f45])).
% 2.02/0.63  fof(f45,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f37,f36])).
% 2.02/0.63  fof(f36,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f9])).
% 2.02/0.63  fof(f9,axiom,(
% 2.02/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.02/0.63  fof(f37,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f8])).
% 2.02/0.63  fof(f8,axiom,(
% 2.02/0.63    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.02/0.63  fof(f106,plain,(
% 2.02/0.63    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8) = X8) )),
% 2.02/0.63    inference(forward_demodulation,[],[f100,f46])).
% 2.02/0.63  fof(f46,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.02/0.63    inference(definition_unfolding,[],[f38,f36])).
% 2.02/0.63  fof(f38,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.02/0.63    inference(cnf_transformation,[],[f12])).
% 2.02/0.63  fof(f12,axiom,(
% 2.02/0.63    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.02/0.63  fof(f100,plain,(
% 2.02/0.63    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8) = k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 2.02/0.63    inference(superposition,[],[f35,f45])).
% 2.02/0.63  fof(f35,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f6])).
% 2.02/0.63  fof(f6,axiom,(
% 2.02/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.02/0.63  fof(f530,plain,(
% 2.02/0.63    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f529,f34])).
% 2.02/0.63  fof(f529,plain,(
% 2.02/0.63    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f495,f31])).
% 2.02/0.63  fof(f31,plain,(
% 2.02/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.02/0.63    inference(cnf_transformation,[],[f7])).
% 2.02/0.63  fof(f7,axiom,(
% 2.02/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.02/0.63  fof(f495,plain,(
% 2.02/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) )),
% 2.02/0.63    inference(superposition,[],[f51,f52])).
% 2.02/0.63  fof(f52,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.02/0.63    inference(backward_demodulation,[],[f44,f31])).
% 2.02/0.63  fof(f44,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f29,f36])).
% 2.02/0.63  fof(f29,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f5])).
% 2.02/0.63  fof(f5,axiom,(
% 2.02/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.02/0.63  fof(f51,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f43,f36])).
% 2.02/0.63  fof(f43,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f13])).
% 2.02/0.63  fof(f13,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.02/0.63  fof(f2956,plain,(
% 2.02/0.63    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 2.02/0.63    inference(superposition,[],[f532,f556])).
% 2.02/0.63  fof(f556,plain,(
% 2.02/0.63    ( ! [X16] : (k4_xboole_0(sK0,X16) = k4_xboole_0(sK0,k4_xboole_0(X16,k4_xboole_0(sK1,sK2)))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f555,f30])).
% 2.02/0.63  fof(f30,plain,(
% 2.02/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.02/0.63    inference(cnf_transformation,[],[f4])).
% 2.02/0.63  fof(f4,axiom,(
% 2.02/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.02/0.63  fof(f555,plain,(
% 2.02/0.63    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(X16,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X16),k1_xboole_0)) )),
% 2.02/0.63    inference(forward_demodulation,[],[f500,f52])).
% 2.02/0.63  fof(f500,plain,(
% 2.02/0.63    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(X16,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X16),k4_xboole_0(sK0,sK0))) )),
% 2.02/0.63    inference(superposition,[],[f51,f123])).
% 2.02/0.63  fof(f123,plain,(
% 2.02/0.63    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.02/0.63    inference(forward_demodulation,[],[f117,f31])).
% 2.02/0.63  fof(f117,plain,(
% 2.02/0.63    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.02/0.63    inference(superposition,[],[f45,f81])).
% 2.02/0.63  fof(f81,plain,(
% 2.02/0.63    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.02/0.63    inference(resolution,[],[f69,f27])).
% 2.02/0.63  fof(f27,plain,(
% 2.02/0.63    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.02/0.63    inference(cnf_transformation,[],[f22])).
% 2.02/0.63  fof(f69,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.63    inference(resolution,[],[f47,f32])).
% 2.02/0.63  fof(f32,plain,(
% 2.02/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.02/0.63    inference(cnf_transformation,[],[f24])).
% 2.02/0.63  fof(f24,plain,(
% 2.02/0.63    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).
% 2.02/0.63  fof(f23,plain,(
% 2.02/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f19,plain,(
% 2.02/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.02/0.63    inference(ennf_transformation,[],[f3])).
% 2.02/0.63  fof(f3,axiom,(
% 2.02/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.02/0.63  fof(f47,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.02/0.63    inference(definition_unfolding,[],[f40,f36])).
% 2.02/0.63  fof(f40,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f26])).
% 2.02/0.63  fof(f26,plain,(
% 2.02/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f25])).
% 2.02/0.63  fof(f25,plain,(
% 2.02/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f20,plain,(
% 2.02/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.63    inference(ennf_transformation,[],[f17])).
% 2.02/0.63  fof(f17,plain,(
% 2.02/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.63    inference(rectify,[],[f2])).
% 2.02/0.63  fof(f2,axiom,(
% 2.02/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.02/0.63  fof(f532,plain,(
% 2.02/0.63    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X4,k4_xboole_0(X6,X5))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f496,f51])).
% 2.02/0.63  fof(f496,plain,(
% 2.02/0.63    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X4,k4_xboole_0(X4,X5)))) )),
% 2.02/0.63    inference(superposition,[],[f51,f45])).
% 2.02/0.63  fof(f33,plain,(
% 2.02/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f14])).
% 2.02/0.63  fof(f14,axiom,(
% 2.02/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.02/0.63  % SZS output end Proof for theBenchmark
% 2.02/0.63  % (28760)------------------------------
% 2.02/0.63  % (28760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (28760)Termination reason: Refutation
% 2.02/0.63  
% 2.02/0.63  % (28760)Memory used [KB]: 3454
% 2.02/0.63  % (28760)Time elapsed: 0.182 s
% 2.02/0.63  % (28760)------------------------------
% 2.02/0.63  % (28760)------------------------------
% 2.02/0.63  % (28756)Success in time 0.256 s
%------------------------------------------------------------------------------
