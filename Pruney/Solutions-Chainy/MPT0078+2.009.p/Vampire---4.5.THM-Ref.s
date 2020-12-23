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
% DateTime   : Thu Dec  3 12:30:48 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   90 (1447 expanded)
%              Number of leaves         :   11 ( 415 expanded)
%              Depth                    :   32
%              Number of atoms          :  116 (2437 expanded)
%              Number of equality atoms :   83 (1511 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f924,plain,(
    $false ),
    inference(subsumption_resolution,[],[f923,f22])).

fof(f22,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f923,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f922,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f922,plain,(
    sK2 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f918,f782])).

fof(f782,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f781,f24])).

fof(f781,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f779,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f779,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f30,f758])).

fof(f758,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f48,f752])).

fof(f752,plain,(
    sK2 = k4_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f47,f732])).

fof(f732,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f718,f500])).

fof(f500,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f299,f499])).

fof(f499,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f496,f485])).

fof(f485,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f484,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f484,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f69,f143])).

fof(f143,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f134,f100])).

fof(f100,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f99,f28])).

fof(f99,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f95,f30])).

fof(f95,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f94,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f94,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f93,f88])).

fof(f88,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f53,f49])).

fof(f49,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f41,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f40,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f21,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f21,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f36,f47])).

fof(f93,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f31,f92])).

fof(f92,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f91,f24])).

fof(f91,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f90,f28])).

fof(f90,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f30,f88])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f134,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f55,f42])).

fof(f42,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f19,f28])).

% (16074)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f19,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f51,f34])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f34,f47])).

fof(f69,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f36,f50])).

fof(f50,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f31,f42])).

fof(f496,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f31,f481])).

fof(f481,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f480,f42])).

fof(f480,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f479,f28])).

fof(f479,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f469,f30])).

fof(f469,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f326,f79])).

fof(f79,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f66,f28])).

fof(f66,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f65,f24])).

fof(f65,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f30,f49])).

fof(f326,plain,(
    ! [X1] : k2_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k2_xboole_0(sK2,k2_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f147,f28])).

fof(f147,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(sK1,X2),sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,X2)) ),
    inference(forward_demodulation,[],[f146,f28])).

fof(f146,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(sK1,X2),sK2) = k2_xboole_0(k2_xboole_0(sK1,X2),sK0) ),
    inference(forward_demodulation,[],[f142,f30])).

fof(f142,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(sK1,X2),sK2) = k2_xboole_0(k2_xboole_0(sK1,X2),k4_xboole_0(sK0,k2_xboole_0(sK1,X2))) ),
    inference(superposition,[],[f30,f55])).

fof(f299,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f138,f66])).

fof(f138,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f55,f28])).

fof(f718,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f507,f66])).

fof(f507,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f34,f500])).

fof(f47,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f44,f31])).

fof(f44,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f31,f19])).

fof(f48,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f39,f26])).

fof(f39,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f20,f38])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f918,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f30,f899])).

fof(f899,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f805,f100])).

fof(f805,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f773,f28])).

fof(f773,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f34,f752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:42:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (16075)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (16067)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (16086)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (16069)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16068)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (16085)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (16078)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (16071)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (16065)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (16072)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (16083)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (16070)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (16073)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (16088)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (16077)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (16066)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (16080)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (16091)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (16090)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (16089)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (16092)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (16087)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (16075)Refutation not found, incomplete strategy% (16075)------------------------------
% 1.36/0.54  % (16075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (16075)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (16075)Memory used [KB]: 10618
% 1.36/0.54  % (16075)Time elapsed: 0.129 s
% 1.36/0.54  % (16075)------------------------------
% 1.36/0.54  % (16075)------------------------------
% 1.36/0.55  % (16064)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.55  % (16084)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (16093)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (16082)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (16085)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f924,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(subsumption_resolution,[],[f923,f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    sK0 != sK2),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,plain,(
% 1.36/0.55    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 1.36/0.55    inference(flattening,[],[f15])).
% 1.36/0.55  fof(f15,plain,(
% 1.36/0.55    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.36/0.55    inference(negated_conjecture,[],[f12])).
% 1.36/0.55  fof(f12,conjecture,(
% 1.36/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.36/0.55  fof(f923,plain,(
% 1.36/0.55    sK0 = sK2),
% 1.36/0.55    inference(forward_demodulation,[],[f922,f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f5])).
% 1.36/0.55  fof(f5,axiom,(
% 1.36/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.36/0.55  fof(f922,plain,(
% 1.36/0.55    sK2 = k2_xboole_0(sK0,k1_xboole_0)),
% 1.36/0.55    inference(forward_demodulation,[],[f918,f782])).
% 1.36/0.55  fof(f782,plain,(
% 1.36/0.55    sK2 = k2_xboole_0(sK0,sK2)),
% 1.36/0.55    inference(forward_demodulation,[],[f781,f24])).
% 1.36/0.55  fof(f781,plain,(
% 1.36/0.55    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 1.36/0.55    inference(forward_demodulation,[],[f779,f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.36/0.55  fof(f779,plain,(
% 1.36/0.55    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK0)),
% 1.36/0.55    inference(superposition,[],[f30,f758])).
% 1.36/0.55  fof(f758,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 1.36/0.55    inference(backward_demodulation,[],[f48,f752])).
% 1.36/0.55  fof(f752,plain,(
% 1.36/0.55    sK2 = k4_xboole_0(sK0,sK1)),
% 1.36/0.55    inference(backward_demodulation,[],[f47,f732])).
% 1.36/0.55  fof(f732,plain,(
% 1.36/0.55    sK2 = k4_xboole_0(sK2,sK1)),
% 1.36/0.55    inference(forward_demodulation,[],[f718,f500])).
% 1.36/0.55  fof(f500,plain,(
% 1.36/0.55    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(backward_demodulation,[],[f299,f499])).
% 1.36/0.55  fof(f499,plain,(
% 1.36/0.55    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f496,f485])).
% 1.36/0.55  fof(f485,plain,(
% 1.36/0.55    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f484,f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.36/0.55  fof(f484,plain,(
% 1.36/0.55    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.36/0.55    inference(forward_demodulation,[],[f69,f143])).
% 1.36/0.55  fof(f143,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(forward_demodulation,[],[f134,f100])).
% 1.36/0.55  fof(f100,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(forward_demodulation,[],[f99,f28])).
% 1.36/0.55  fof(f99,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 1.36/0.55    inference(forward_demodulation,[],[f95,f30])).
% 1.36/0.55  fof(f95,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 1.36/0.55    inference(superposition,[],[f94,f34])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.36/0.55  fof(f94,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(forward_demodulation,[],[f93,f88])).
% 1.36/0.55  fof(f88,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(forward_demodulation,[],[f53,f49])).
% 1.36/0.55  fof(f49,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(resolution,[],[f41,f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,plain,(
% 1.36/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.36/0.55    inference(ennf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f40,f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f27,f29,f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) )),
% 1.36/0.55    inference(resolution,[],[f21,f38])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f32,f29])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,plain,(
% 1.36/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,plain,(
% 1.36/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.55    inference(rectify,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    r1_xboole_0(sK2,sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f53,plain,(
% 1.36/0.55    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(superposition,[],[f36,f47])).
% 1.36/0.55  fof(f93,plain,(
% 1.36/0.55    k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(superposition,[],[f31,f92])).
% 1.36/0.55  fof(f92,plain,(
% 1.36/0.55    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(forward_demodulation,[],[f91,f24])).
% 1.36/0.55  fof(f91,plain,(
% 1.36/0.55    k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(forward_demodulation,[],[f90,f28])).
% 1.36/0.55  fof(f90,plain,(
% 1.36/0.55    k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 1.36/0.55    inference(superposition,[],[f30,f88])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.36/0.55  fof(f134,plain,(
% 1.36/0.55    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(superposition,[],[f55,f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 1.36/0.55    inference(superposition,[],[f19,f28])).
% 1.36/0.55  % (16074)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f55,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f51,f34])).
% 1.36/0.55  fof(f51,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(k4_xboole_0(sK0,sK1),X0)) )),
% 1.36/0.55    inference(superposition,[],[f34,f47])).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(superposition,[],[f36,f50])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 1.36/0.55    inference(superposition,[],[f31,f42])).
% 1.36/0.55  fof(f496,plain,(
% 1.36/0.55    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(superposition,[],[f31,f481])).
% 1.36/0.55  fof(f481,plain,(
% 1.36/0.55    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f480,f42])).
% 1.36/0.55  fof(f480,plain,(
% 1.36/0.55    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f479,f28])).
% 1.36/0.55  fof(f479,plain,(
% 1.36/0.55    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f469,f30])).
% 1.36/0.55  fof(f469,plain,(
% 1.36/0.55    k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(superposition,[],[f326,f79])).
% 1.36/0.55  fof(f79,plain,(
% 1.36/0.55    k4_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(superposition,[],[f66,f28])).
% 1.36/0.55  fof(f66,plain,(
% 1.36/0.55    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 1.36/0.55    inference(forward_demodulation,[],[f65,f24])).
% 1.36/0.55  fof(f65,plain,(
% 1.36/0.55    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 1.36/0.55    inference(superposition,[],[f30,f49])).
% 1.36/0.55  fof(f326,plain,(
% 1.36/0.55    ( ! [X1] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k2_xboole_0(sK2,k2_xboole_0(sK1,X1))) )),
% 1.36/0.55    inference(superposition,[],[f147,f28])).
% 1.36/0.55  fof(f147,plain,(
% 1.36/0.55    ( ! [X2] : (k2_xboole_0(k2_xboole_0(sK1,X2),sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,X2))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f146,f28])).
% 1.36/0.55  fof(f146,plain,(
% 1.36/0.55    ( ! [X2] : (k2_xboole_0(k2_xboole_0(sK1,X2),sK2) = k2_xboole_0(k2_xboole_0(sK1,X2),sK0)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f142,f30])).
% 1.36/0.55  fof(f142,plain,(
% 1.36/0.55    ( ! [X2] : (k2_xboole_0(k2_xboole_0(sK1,X2),sK2) = k2_xboole_0(k2_xboole_0(sK1,X2),k4_xboole_0(sK0,k2_xboole_0(sK1,X2)))) )),
% 1.36/0.55    inference(superposition,[],[f30,f55])).
% 1.36/0.55  fof(f299,plain,(
% 1.36/0.55    k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(superposition,[],[f138,f66])).
% 1.36/0.55  fof(f138,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))) )),
% 1.36/0.55    inference(superposition,[],[f55,f28])).
% 1.36/0.55  fof(f718,plain,(
% 1.36/0.55    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(superposition,[],[f507,f66])).
% 1.36/0.55  fof(f507,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK2,X0)) )),
% 1.36/0.55    inference(superposition,[],[f34,f500])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1)),
% 1.36/0.55    inference(forward_demodulation,[],[f44,f31])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 1.36/0.55    inference(superposition,[],[f31,f19])).
% 1.36/0.55  fof(f48,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(resolution,[],[f39,f26])).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 1.36/0.55    inference(resolution,[],[f20,f38])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    r1_xboole_0(sK0,sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.36/0.55  fof(f918,plain,(
% 1.36/0.55    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 1.36/0.55    inference(superposition,[],[f30,f899])).
% 1.36/0.55  fof(f899,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 1.36/0.55    inference(superposition,[],[f805,f100])).
% 1.36/0.55  fof(f805,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK2,X0)) )),
% 1.36/0.55    inference(superposition,[],[f773,f28])).
% 1.36/0.55  fof(f773,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.36/0.55    inference(superposition,[],[f34,f752])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (16085)------------------------------
% 1.36/0.55  % (16085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (16085)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (16085)Memory used [KB]: 2174
% 1.36/0.55  % (16085)Time elapsed: 0.125 s
% 1.36/0.55  % (16085)------------------------------
% 1.36/0.55  % (16085)------------------------------
% 1.50/0.56  % (16076)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.56  % (16063)Success in time 0.195 s
%------------------------------------------------------------------------------
