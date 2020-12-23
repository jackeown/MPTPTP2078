%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:20 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 386 expanded)
%              Number of leaves         :   10 ( 122 expanded)
%              Depth                    :   23
%              Number of atoms          :   95 ( 550 expanded)
%              Number of equality atoms :   58 ( 325 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f819,plain,(
    $false ),
    inference(subsumption_resolution,[],[f818,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f32,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f818,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f55,f801])).

fof(f801,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f791,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f791,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f790,f757])).

fof(f757,plain,(
    ! [X4,X3] : k4_xboole_0(sK0,k4_xboole_0(sK0,X3)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X3,k4_xboole_0(X4,sK2)))) ),
    inference(superposition,[],[f731,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f24,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f731,plain,(
    ! [X8,X7] : k4_xboole_0(sK0,X8) = k4_xboole_0(k4_xboole_0(sK0,X8),k4_xboole_0(X7,sK2)) ),
    inference(superposition,[],[f216,f628])).

fof(f628,plain,(
    ! [X6,X7] : k4_xboole_0(X6,sK2) = k4_xboole_0(k4_xboole_0(X6,sK2),k4_xboole_0(sK0,X7)) ),
    inference(forward_demodulation,[],[f608,f22])).

fof(f608,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,sK2),k4_xboole_0(sK0,X7)) = k4_xboole_0(k4_xboole_0(X6,sK2),k1_xboole_0) ),
    inference(superposition,[],[f33,f291])).

fof(f291,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK0,X2))) ),
    inference(forward_demodulation,[],[f290,f42])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f23,f38])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f290,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK0,X2))) ),
    inference(forward_demodulation,[],[f286,f38])).

fof(f286,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(X1,sK2)),X2) ),
    inference(superposition,[],[f36,f257])).

fof(f257,plain,(
    ! [X14] : k4_xboole_0(X14,sK2) = k4_xboole_0(k4_xboole_0(X14,sK2),sK0) ),
    inference(superposition,[],[f216,f224])).

fof(f224,plain,(
    ! [X19] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2)) ),
    inference(forward_demodulation,[],[f203,f22])).

fof(f203,plain,(
    ! [X19] : k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X19,sK2)) ),
    inference(superposition,[],[f148,f96])).

fof(f96,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f36,f43])).

fof(f43,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f28,f23])).

fof(f148,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) ),
    inference(forward_demodulation,[],[f137,f120])).

fof(f120,plain,(
    ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16) ),
    inference(forward_demodulation,[],[f91,f22])).

fof(f91,plain,(
    ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X16) ),
    inference(superposition,[],[f36,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f137,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) ),
    inference(superposition,[],[f120,f33])).

fof(f216,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4 ),
    inference(forward_demodulation,[],[f197,f22])).

fof(f197,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f33,f96])).

fof(f790,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(forward_demodulation,[],[f776,f139])).

fof(f139,plain,(
    ! [X2] : k4_xboole_0(sK0,k4_xboole_0(sK2,X2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f33,f120])).

fof(f776,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[],[f507,f139])).

fof(f507,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[],[f379,f79])).

fof(f79,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f68,f22])).

fof(f68,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f33,f56])).

fof(f56,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f379,plain,(
    ! [X18] : k4_xboole_0(sK0,X18) = k4_xboole_0(k4_xboole_0(sK0,X18),k4_xboole_0(sK2,k4_xboole_0(sK2,X18))) ),
    inference(superposition,[],[f249,f148])).

fof(f249,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(superposition,[],[f216,f216])).

fof(f55,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f34,f18])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (25136)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (25149)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (25139)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (25146)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (25138)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (25141)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (25145)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (25143)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (25135)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (25137)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (25147)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (25144)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.37/0.54  % (25147)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f819,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(subsumption_resolution,[],[f818,f38])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.37/0.54    inference(backward_demodulation,[],[f32,f22])).
% 1.37/0.54  fof(f22,plain,(
% 1.37/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f21,f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.37/0.54  fof(f21,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.37/0.54  fof(f818,plain,(
% 1.37/0.54    k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 1.37/0.54    inference(backward_demodulation,[],[f55,f801])).
% 1.37/0.54  fof(f801,plain,(
% 1.37/0.54    sK0 = k4_xboole_0(sK0,sK1)),
% 1.37/0.54    inference(superposition,[],[f791,f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f25,f24])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.37/0.54  fof(f791,plain,(
% 1.37/0.54    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.37/0.54    inference(forward_demodulation,[],[f790,f757])).
% 1.37/0.54  fof(f757,plain,(
% 1.37/0.54    ( ! [X4,X3] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X3)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X3,k4_xboole_0(X4,sK2))))) )),
% 1.37/0.54    inference(superposition,[],[f731,f36])).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f29,f24,f24])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f8])).
% 1.37/0.54  fof(f8,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.37/0.54  fof(f731,plain,(
% 1.37/0.54    ( ! [X8,X7] : (k4_xboole_0(sK0,X8) = k4_xboole_0(k4_xboole_0(sK0,X8),k4_xboole_0(X7,sK2))) )),
% 1.37/0.54    inference(superposition,[],[f216,f628])).
% 1.37/0.54  fof(f628,plain,(
% 1.37/0.54    ( ! [X6,X7] : (k4_xboole_0(X6,sK2) = k4_xboole_0(k4_xboole_0(X6,sK2),k4_xboole_0(sK0,X7))) )),
% 1.37/0.54    inference(forward_demodulation,[],[f608,f22])).
% 1.37/0.54  fof(f608,plain,(
% 1.37/0.54    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,sK2),k4_xboole_0(sK0,X7)) = k4_xboole_0(k4_xboole_0(X6,sK2),k1_xboole_0)) )),
% 1.37/0.54    inference(superposition,[],[f33,f291])).
% 1.37/0.54  fof(f291,plain,(
% 1.37/0.54    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK0,X2)))) )),
% 1.37/0.54    inference(forward_demodulation,[],[f290,f42])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.37/0.54    inference(resolution,[],[f28,f40])).
% 1.37/0.54  fof(f40,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.37/0.54    inference(superposition,[],[f23,f38])).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,plain,(
% 1.37/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f12])).
% 1.37/0.54  fof(f12,plain,(
% 1.37/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 1.37/0.54    inference(unused_predicate_definition_removal,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.37/0.54  fof(f290,plain,(
% 1.37/0.54    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK0,X2)))) )),
% 1.37/0.54    inference(forward_demodulation,[],[f286,f38])).
% 1.37/0.54  fof(f286,plain,(
% 1.37/0.54    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(sK0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK2),k4_xboole_0(X1,sK2)),X2)) )),
% 1.37/0.54    inference(superposition,[],[f36,f257])).
% 1.37/0.54  fof(f257,plain,(
% 1.37/0.54    ( ! [X14] : (k4_xboole_0(X14,sK2) = k4_xboole_0(k4_xboole_0(X14,sK2),sK0)) )),
% 1.37/0.54    inference(superposition,[],[f216,f224])).
% 1.37/0.54  fof(f224,plain,(
% 1.37/0.54    ( ! [X19] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2))) )),
% 1.37/0.54    inference(forward_demodulation,[],[f203,f22])).
% 1.37/0.54  fof(f203,plain,(
% 1.37/0.54    ( ! [X19] : (k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X19,sK2))) )),
% 1.37/0.54    inference(superposition,[],[f148,f96])).
% 1.37/0.54  fof(f96,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.37/0.54    inference(superposition,[],[f36,f43])).
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 1.37/0.54    inference(resolution,[],[f28,f23])).
% 1.37/0.54  fof(f148,plain,(
% 1.37/0.54    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) )),
% 1.37/0.54    inference(forward_demodulation,[],[f137,f120])).
% 1.37/0.54  fof(f120,plain,(
% 1.37/0.54    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16)) )),
% 1.37/0.54    inference(forward_demodulation,[],[f91,f22])).
% 1.37/0.54  fof(f91,plain,(
% 1.37/0.54    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X16)) )),
% 1.37/0.54    inference(superposition,[],[f36,f44])).
% 1.37/0.54  fof(f44,plain,(
% 1.37/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 1.37/0.54    inference(resolution,[],[f28,f19])).
% 1.37/0.54  fof(f19,plain,(
% 1.37/0.54    r1_tarski(sK0,sK2)),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,plain,(
% 1.37/0.54    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 1.37/0.54  fof(f15,plain,(
% 1.37/0.54    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f13,plain,(
% 1.37/0.54    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,negated_conjecture,(
% 1.37/0.54    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.37/0.54    inference(negated_conjecture,[],[f10])).
% 1.37/0.54  fof(f10,conjecture,(
% 1.37/0.54    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 1.37/0.54  fof(f137,plain,(
% 1.37/0.54    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) )),
% 1.37/0.54    inference(superposition,[],[f120,f33])).
% 1.37/0.54  fof(f216,plain,(
% 1.37/0.54    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) )),
% 1.37/0.54    inference(forward_demodulation,[],[f197,f22])).
% 1.37/0.54  fof(f197,plain,(
% 1.37/0.54    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,k1_xboole_0)) )),
% 1.37/0.54    inference(superposition,[],[f33,f96])).
% 1.37/0.54  fof(f790,plain,(
% 1.37/0.54    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),
% 1.37/0.54    inference(forward_demodulation,[],[f776,f139])).
% 1.37/0.54  fof(f139,plain,(
% 1.37/0.54    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X2))) )),
% 1.37/0.54    inference(superposition,[],[f33,f120])).
% 1.37/0.54  fof(f776,plain,(
% 1.37/0.54    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),
% 1.37/0.54    inference(superposition,[],[f507,f139])).
% 1.37/0.54  fof(f507,plain,(
% 1.37/0.54    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),
% 1.37/0.54    inference(superposition,[],[f379,f79])).
% 1.37/0.54  fof(f79,plain,(
% 1.37/0.54    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.37/0.54    inference(forward_demodulation,[],[f68,f22])).
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.37/0.54    inference(superposition,[],[f33,f56])).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.37/0.54    inference(resolution,[],[f35,f31])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.37/0.54    inference(definition_unfolding,[],[f20,f24])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f26,f24])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,plain,(
% 1.37/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.37/0.54    inference(nnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.37/0.54  fof(f379,plain,(
% 1.37/0.54    ( ! [X18] : (k4_xboole_0(sK0,X18) = k4_xboole_0(k4_xboole_0(sK0,X18),k4_xboole_0(sK2,k4_xboole_0(sK2,X18)))) )),
% 1.37/0.54    inference(superposition,[],[f249,f148])).
% 1.37/0.54  fof(f249,plain,(
% 1.37/0.54    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 1.37/0.54    inference(superposition,[],[f216,f216])).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.37/0.54    inference(resolution,[],[f34,f18])).
% 1.37/0.54  fof(f18,plain,(
% 1.37/0.54    ~r1_xboole_0(sK0,sK1)),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f27,f24])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f17])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (25147)------------------------------
% 1.37/0.54  % (25147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (25147)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (25147)Memory used [KB]: 6524
% 1.37/0.54  % (25147)Time elapsed: 0.082 s
% 1.37/0.54  % (25147)------------------------------
% 1.37/0.54  % (25147)------------------------------
% 1.37/0.55  % (25140)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.37/0.55  % (25132)Success in time 0.178 s
%------------------------------------------------------------------------------
