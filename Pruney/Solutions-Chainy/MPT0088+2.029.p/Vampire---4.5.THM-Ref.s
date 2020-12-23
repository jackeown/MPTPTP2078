%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:34 EST 2020

% Result     : Theorem 7.74s
% Output     : Refutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 355 expanded)
%              Number of leaves         :   10 ( 119 expanded)
%              Depth                    :   21
%              Number of atoms          :   89 ( 399 expanded)
%              Number of equality atoms :   60 ( 327 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29030,plain,(
    $false ),
    inference(resolution,[],[f28976,f16])).

fof(f16,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f28976,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f28819,f780])).

fof(f780,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f24,f756])).

fof(f756,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f716,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f716,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f80,f39])).

fof(f39,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f28,f15])).

fof(f15,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f80,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f79,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f24,f18])).

fof(f79,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,X3)) ),
    inference(forward_demodulation,[],[f60,f24])).

fof(f60,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3) ),
    inference(superposition,[],[f29,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f26,f18])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f20,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f28819,plain,(
    ! [X288,X287,X286] : r1_xboole_0(X286,k4_xboole_0(X288,k2_xboole_0(k4_xboole_0(X286,X287),X287))) ),
    inference(forward_demodulation,[],[f28648,f18])).

fof(f28648,plain,(
    ! [X288,X287,X286] : r1_xboole_0(k4_xboole_0(X286,k1_xboole_0),k4_xboole_0(X288,k2_xboole_0(k4_xboole_0(X286,X287),X287))) ),
    inference(superposition,[],[f7241,f27955])).

fof(f27955,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X6)) ),
    inference(superposition,[],[f26647,f24])).

fof(f26647,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(forward_demodulation,[],[f26646,f491])).

fof(f491,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f467,f31])).

fof(f467,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f201,f18])).

fof(f201,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f200,f18])).

fof(f200,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f176,f83])).

fof(f83,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(forward_demodulation,[],[f82,f37])).

fof(f37,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f19,f31])).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f82,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),X5))) ),
    inference(forward_demodulation,[],[f81,f47])).

fof(f81,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),X5))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f61,f24])).

fof(f61,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),X5))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X5) ),
    inference(superposition,[],[f29,f37])).

fof(f176,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f30,f18])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f26646,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f26645,f31])).

fof(f26645,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(forward_demodulation,[],[f26195,f18])).

fof(f26195,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) ),
    inference(superposition,[],[f330,f31])).

fof(f330,plain,(
    ! [X14,X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k2_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))))) ),
    inference(superposition,[],[f53,f29])).

fof(f53,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f24,f31])).

fof(f7241,plain,(
    ! [X64,X62,X63] : r1_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,X62)),k4_xboole_0(X63,X62)) ),
    inference(backward_demodulation,[],[f6636,f7236])).

fof(f7236,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X16,X18) = k4_xboole_0(X16,k4_xboole_0(X18,k4_xboole_0(X17,X16))) ),
    inference(forward_demodulation,[],[f7109,f217])).

fof(f217,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f216,f18])).

fof(f216,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f185,f31])).

fof(f185,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f30,f18])).

fof(f7109,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X16,k4_xboole_0(X18,k4_xboole_0(X17,X16))) = k2_xboole_0(k4_xboole_0(X16,X18),k1_xboole_0) ),
    inference(superposition,[],[f30,f5274])).

fof(f5274,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f5082,f29])).

fof(f5082,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(forward_demodulation,[],[f4966,f18])).

fof(f4966,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f198,f31])).

fof(f198,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f87,f30])).

fof(f87,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f48,f83])).

fof(f48,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f24,f31])).

fof(f6636,plain,(
    ! [X64,X62,X63] : r1_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,X62)),k4_xboole_0(X63,k4_xboole_0(X62,k4_xboole_0(X62,X63)))) ),
    inference(superposition,[],[f74,f1182])).

fof(f1182,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) = X3 ),
    inference(forward_demodulation,[],[f1103,f18])).

fof(f1103,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) ),
    inference(superposition,[],[f80,f71])).

fof(f71,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,X9))))) ),
    inference(superposition,[],[f29,f31])).

fof(f74,plain,(
    ! [X6,X8,X7] : r1_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))),X8) ),
    inference(superposition,[],[f19,f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (22704)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.45  % (22711)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.45  % (22705)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.46  % (22719)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.46  % (22709)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.46  % (22707)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  % (22718)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (22706)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (22720)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.47  % (22710)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.47  % (22714)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.47  % (22713)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.47  % (22715)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.48  % (22712)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.48  % (22717)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.48  % (22716)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.49  % (22721)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.50  % (22708)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 5.19/1.02  % (22708)Time limit reached!
% 5.19/1.02  % (22708)------------------------------
% 5.19/1.02  % (22708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.19/1.02  % (22708)Termination reason: Time limit
% 5.19/1.02  
% 5.19/1.02  % (22708)Memory used [KB]: 14456
% 5.19/1.02  % (22708)Time elapsed: 0.620 s
% 5.19/1.02  % (22708)------------------------------
% 5.19/1.02  % (22708)------------------------------
% 7.74/1.34  % (22705)Refutation found. Thanks to Tanya!
% 7.74/1.34  % SZS status Theorem for theBenchmark
% 7.74/1.35  % SZS output start Proof for theBenchmark
% 7.74/1.35  fof(f29030,plain,(
% 7.74/1.35    $false),
% 7.74/1.35    inference(resolution,[],[f28976,f16])).
% 7.74/1.35  fof(f16,plain,(
% 7.74/1.35    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.74/1.35    inference(cnf_transformation,[],[f13])).
% 7.74/1.35  fof(f13,plain,(
% 7.74/1.35    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.74/1.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 7.74/1.35  fof(f12,plain,(
% 7.74/1.35    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 7.74/1.35    introduced(choice_axiom,[])).
% 7.74/1.35  fof(f11,plain,(
% 7.74/1.35    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 7.74/1.35    inference(ennf_transformation,[],[f10])).
% 7.74/1.35  fof(f10,negated_conjecture,(
% 7.74/1.35    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.74/1.35    inference(negated_conjecture,[],[f9])).
% 7.74/1.35  fof(f9,conjecture,(
% 7.74/1.35    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 7.74/1.35  fof(f28976,plain,(
% 7.74/1.35    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.74/1.35    inference(superposition,[],[f28819,f780])).
% 7.74/1.35  fof(f780,plain,(
% 7.74/1.35    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) )),
% 7.74/1.35    inference(superposition,[],[f24,f756])).
% 7.74/1.35  fof(f756,plain,(
% 7.74/1.35    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.74/1.35    inference(forward_demodulation,[],[f716,f18])).
% 7.74/1.35  fof(f18,plain,(
% 7.74/1.35    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.74/1.35    inference(cnf_transformation,[],[f3])).
% 7.74/1.35  fof(f3,axiom,(
% 7.74/1.35    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 7.74/1.35  fof(f716,plain,(
% 7.74/1.35    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 7.74/1.35    inference(superposition,[],[f80,f39])).
% 7.74/1.35  fof(f39,plain,(
% 7.74/1.35    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 7.74/1.35    inference(resolution,[],[f28,f15])).
% 7.74/1.35  fof(f15,plain,(
% 7.74/1.35    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.74/1.35    inference(cnf_transformation,[],[f13])).
% 7.74/1.35  fof(f28,plain,(
% 7.74/1.35    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.74/1.35    inference(definition_unfolding,[],[f21,f20])).
% 7.74/1.35  fof(f20,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.74/1.35    inference(cnf_transformation,[],[f5])).
% 7.74/1.35  fof(f5,axiom,(
% 7.74/1.35    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 7.74/1.35  fof(f21,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.35    inference(cnf_transformation,[],[f14])).
% 7.74/1.35  fof(f14,plain,(
% 7.74/1.35    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.74/1.35    inference(nnf_transformation,[],[f1])).
% 7.74/1.35  fof(f1,axiom,(
% 7.74/1.35    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 7.74/1.35  fof(f80,plain,(
% 7.74/1.35    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f79,f47])).
% 7.74/1.35  fof(f47,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 7.74/1.35    inference(superposition,[],[f24,f18])).
% 7.74/1.35  fof(f79,plain,(
% 7.74/1.35    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,X3))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f60,f24])).
% 7.74/1.35  fof(f60,plain,(
% 7.74/1.35    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)) )),
% 7.74/1.35    inference(superposition,[],[f29,f31])).
% 7.74/1.35  fof(f31,plain,(
% 7.74/1.35    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 7.74/1.35    inference(backward_demodulation,[],[f26,f18])).
% 7.74/1.35  fof(f26,plain,(
% 7.74/1.35    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.74/1.35    inference(definition_unfolding,[],[f17,f20])).
% 7.74/1.35  fof(f17,plain,(
% 7.74/1.35    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.74/1.35    inference(cnf_transformation,[],[f2])).
% 7.74/1.35  fof(f2,axiom,(
% 7.74/1.35    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 7.74/1.35  fof(f29,plain,(
% 7.74/1.35    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.74/1.35    inference(definition_unfolding,[],[f23,f20,f20])).
% 7.74/1.35  fof(f23,plain,(
% 7.74/1.35    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.74/1.35    inference(cnf_transformation,[],[f6])).
% 7.74/1.35  fof(f6,axiom,(
% 7.74/1.35    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 7.74/1.35  fof(f24,plain,(
% 7.74/1.35    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.74/1.35    inference(cnf_transformation,[],[f4])).
% 7.74/1.35  fof(f4,axiom,(
% 7.74/1.35    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.74/1.35  fof(f28819,plain,(
% 7.74/1.35    ( ! [X288,X287,X286] : (r1_xboole_0(X286,k4_xboole_0(X288,k2_xboole_0(k4_xboole_0(X286,X287),X287)))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f28648,f18])).
% 7.74/1.35  fof(f28648,plain,(
% 7.74/1.35    ( ! [X288,X287,X286] : (r1_xboole_0(k4_xboole_0(X286,k1_xboole_0),k4_xboole_0(X288,k2_xboole_0(k4_xboole_0(X286,X287),X287)))) )),
% 7.74/1.35    inference(superposition,[],[f7241,f27955])).
% 7.74/1.35  fof(f27955,plain,(
% 7.74/1.35    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X6))) )),
% 7.74/1.35    inference(superposition,[],[f26647,f24])).
% 7.74/1.35  fof(f26647,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 7.74/1.35    inference(forward_demodulation,[],[f26646,f491])).
% 7.74/1.35  fof(f491,plain,(
% 7.74/1.35    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.74/1.35    inference(forward_demodulation,[],[f467,f31])).
% 7.74/1.35  fof(f467,plain,(
% 7.74/1.35    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.74/1.35    inference(superposition,[],[f201,f18])).
% 7.74/1.35  fof(f201,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 7.74/1.35    inference(forward_demodulation,[],[f200,f18])).
% 7.74/1.35  fof(f200,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f176,f83])).
% 7.74/1.35  fof(f83,plain,(
% 7.74/1.35    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 7.74/1.35    inference(forward_demodulation,[],[f82,f37])).
% 7.74/1.35  fof(f37,plain,(
% 7.74/1.35    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 7.74/1.35    inference(resolution,[],[f28,f33])).
% 7.74/1.35  fof(f33,plain,(
% 7.74/1.35    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 7.74/1.35    inference(superposition,[],[f19,f31])).
% 7.74/1.35  fof(f19,plain,(
% 7.74/1.35    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.74/1.35    inference(cnf_transformation,[],[f8])).
% 7.74/1.35  fof(f8,axiom,(
% 7.74/1.35    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 7.74/1.35  fof(f82,plain,(
% 7.74/1.35    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),X5)))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f81,f47])).
% 7.74/1.35  fof(f81,plain,(
% 7.74/1.35    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),X5))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f61,f24])).
% 7.74/1.35  fof(f61,plain,(
% 7.74/1.35    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),X5))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X5)) )),
% 7.74/1.35    inference(superposition,[],[f29,f37])).
% 7.74/1.35  fof(f176,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.74/1.35    inference(superposition,[],[f30,f18])).
% 7.74/1.35  fof(f30,plain,(
% 7.74/1.35    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 7.74/1.35    inference(definition_unfolding,[],[f25,f20])).
% 7.74/1.35  fof(f25,plain,(
% 7.74/1.35    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.74/1.35    inference(cnf_transformation,[],[f7])).
% 7.74/1.35  fof(f7,axiom,(
% 7.74/1.35    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.74/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 7.74/1.35  fof(f26646,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,k1_xboole_0))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f26645,f31])).
% 7.74/1.35  fof(f26645,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,k4_xboole_0(X1,X1)))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f26195,f18])).
% 7.74/1.35  fof(f26195,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))))) )),
% 7.74/1.35    inference(superposition,[],[f330,f31])).
% 7.74/1.35  fof(f330,plain,(
% 7.74/1.35    ( ! [X14,X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k2_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))) )),
% 7.74/1.35    inference(superposition,[],[f53,f29])).
% 7.74/1.35  fof(f53,plain,(
% 7.74/1.35    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 7.74/1.35    inference(superposition,[],[f24,f31])).
% 7.74/1.35  fof(f7241,plain,(
% 7.74/1.35    ( ! [X64,X62,X63] : (r1_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,X62)),k4_xboole_0(X63,X62))) )),
% 7.74/1.35    inference(backward_demodulation,[],[f6636,f7236])).
% 7.74/1.35  fof(f7236,plain,(
% 7.74/1.35    ( ! [X17,X18,X16] : (k4_xboole_0(X16,X18) = k4_xboole_0(X16,k4_xboole_0(X18,k4_xboole_0(X17,X16)))) )),
% 7.74/1.35    inference(forward_demodulation,[],[f7109,f217])).
% 7.74/1.35  fof(f217,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 7.74/1.35    inference(forward_demodulation,[],[f216,f18])).
% 7.74/1.35  fof(f216,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 7.74/1.35    inference(forward_demodulation,[],[f185,f31])).
% 7.74/1.35  fof(f185,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) )),
% 7.74/1.35    inference(superposition,[],[f30,f18])).
% 7.74/1.35  fof(f7109,plain,(
% 7.74/1.35    ( ! [X17,X18,X16] : (k4_xboole_0(X16,k4_xboole_0(X18,k4_xboole_0(X17,X16))) = k2_xboole_0(k4_xboole_0(X16,X18),k1_xboole_0)) )),
% 7.74/1.35    inference(superposition,[],[f30,f5274])).
% 7.74/1.35  fof(f5274,plain,(
% 7.74/1.35    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 7.74/1.35    inference(superposition,[],[f5082,f29])).
% 7.74/1.35  fof(f5082,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1)) )),
% 7.74/1.35    inference(forward_demodulation,[],[f4966,f18])).
% 7.74/1.35  fof(f4966,plain,(
% 7.74/1.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0))) )),
% 7.74/1.35    inference(superposition,[],[f198,f31])).
% 7.74/1.35  fof(f198,plain,(
% 7.74/1.35    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 7.74/1.35    inference(superposition,[],[f87,f30])).
% 7.74/1.35  fof(f87,plain,(
% 7.74/1.35    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 7.74/1.35    inference(backward_demodulation,[],[f48,f83])).
% 7.74/1.35  fof(f48,plain,(
% 7.74/1.35    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 7.74/1.35    inference(superposition,[],[f24,f31])).
% 7.74/1.35  fof(f6636,plain,(
% 7.74/1.35    ( ! [X64,X62,X63] : (r1_xboole_0(k4_xboole_0(X64,k4_xboole_0(X64,X62)),k4_xboole_0(X63,k4_xboole_0(X62,k4_xboole_0(X62,X63))))) )),
% 7.74/1.35    inference(superposition,[],[f74,f1182])).
% 7.74/1.35  fof(f1182,plain,(
% 7.74/1.35    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) = X3) )),
% 7.74/1.35    inference(forward_demodulation,[],[f1103,f18])).
% 7.74/1.35  fof(f1103,plain,(
% 7.74/1.35    ( ! [X4,X3] : (k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4))))) )),
% 7.74/1.35    inference(superposition,[],[f80,f71])).
% 7.74/1.35  fof(f71,plain,(
% 7.74/1.35    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,X9)))))) )),
% 7.74/1.35    inference(superposition,[],[f29,f31])).
% 7.74/1.35  fof(f74,plain,(
% 7.74/1.35    ( ! [X6,X8,X7] : (r1_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))),X8)) )),
% 7.74/1.35    inference(superposition,[],[f19,f29])).
% 7.74/1.35  % SZS output end Proof for theBenchmark
% 7.74/1.35  % (22705)------------------------------
% 7.74/1.35  % (22705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.74/1.35  % (22705)Termination reason: Refutation
% 7.74/1.35  
% 7.74/1.35  % (22705)Memory used [KB]: 20980
% 7.74/1.35  % (22705)Time elapsed: 0.939 s
% 7.74/1.35  % (22705)------------------------------
% 7.74/1.35  % (22705)------------------------------
% 7.74/1.36  % (22703)Success in time 1.003 s
%------------------------------------------------------------------------------
