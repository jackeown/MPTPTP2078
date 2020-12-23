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
% DateTime   : Thu Dec  3 12:30:51 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 468 expanded)
%              Number of leaves         :   14 ( 143 expanded)
%              Depth                    :   25
%              Number of atoms          :  118 ( 845 expanded)
%              Number of equality atoms :   91 ( 557 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1641,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1626,f26])).

fof(f26,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1626,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f243,f1622])).

fof(f1622,plain,(
    sK1 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f1621,f1553])).

fof(f1553,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f770,f1527])).

fof(f1527,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f1516,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1516,plain,(
    sK3 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1094,f1509])).

fof(f1509,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1491,f405])).

fof(f405,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f372,f62])).

fof(f62,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f57,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f372,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f41,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f42,f29])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1491,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f748,f23])).

fof(f23,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f748,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f41,f742])).

fof(f742,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f741,f57])).

fof(f741,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f733,f28])).

fof(f733,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f34,f694])).

fof(f694,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f635,f55])).

fof(f635,plain,(
    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f43,f243])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f33,f33])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1094,plain,(
    sK3 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) ),
    inference(forward_demodulation,[],[f1084,f29])).

fof(f1084,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) ),
    inference(superposition,[],[f43,f1020])).

fof(f1020,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f518,f134])).

fof(f134,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f133,f55])).

fof(f133,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f35,f124])).

fof(f124,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f123,f23])).

fof(f123,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f122,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f122,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f117,f34])).

fof(f117,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f34,f104])).

fof(f104,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f35,f23])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f518,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f387,f32])).

fof(f387,plain,(
    ! [X28] : k4_xboole_0(sK3,k2_xboole_0(sK1,X28)) = k4_xboole_0(sK3,X28) ),
    inference(superposition,[],[f41,f262])).

fof(f262,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f261,f57])).

fof(f261,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(forward_demodulation,[],[f255,f28])).

fof(f255,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[],[f34,f234])).

fof(f234,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f45,f25])).

fof(f25,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f770,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f769,f57])).

fof(f769,plain,(
    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f761,f28])).

fof(f761,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f34,f696])).

fof(f696,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f637,f55])).

fof(f637,plain,(
    k4_xboole_0(sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f43,f262])).

fof(f1621,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1610,f99])).

fof(f99,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f35,f32])).

fof(f1610,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f35,f1532])).

fof(f1532,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f23,f1527])).

fof(f243,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f242,f57])).

fof(f242,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f236,f28])).

fof(f236,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f34,f233])).

fof(f233,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (10311)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (10313)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (10305)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (10311)Refutation not found, incomplete strategy% (10311)------------------------------
% 0.21/0.50  % (10311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10300)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (10302)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.52  % (10311)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (10311)Memory used [KB]: 6140
% 1.27/0.52  % (10311)Time elapsed: 0.003 s
% 1.27/0.52  % (10311)------------------------------
% 1.27/0.52  % (10311)------------------------------
% 1.27/0.52  % (10298)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.52  % (10309)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.52  % (10310)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.52  % (10313)Refutation not found, incomplete strategy% (10313)------------------------------
% 1.27/0.52  % (10313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (10313)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (10313)Memory used [KB]: 10618
% 1.27/0.52  % (10313)Time elapsed: 0.113 s
% 1.27/0.52  % (10313)------------------------------
% 1.27/0.52  % (10313)------------------------------
% 1.27/0.52  % (10297)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.52  % (10324)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.53  % (10323)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.53  % (10303)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (10296)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (10317)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.53  % (10299)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.54  % (10301)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.54  % (10319)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.54  % (10316)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (10306)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.54  % (10308)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.54  % (10312)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.54  % (10314)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.54  % (10321)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (10304)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.55  % (10307)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.55  % (10315)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % (10322)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.56  % (10318)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.56  % (10320)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.56  % (10325)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.62  % (10299)Refutation found. Thanks to Tanya!
% 1.40/0.62  % SZS status Theorem for theBenchmark
% 1.40/0.62  % SZS output start Proof for theBenchmark
% 1.40/0.62  fof(f1641,plain,(
% 1.40/0.62    $false),
% 1.40/0.62    inference(subsumption_resolution,[],[f1626,f26])).
% 1.40/0.62  fof(f26,plain,(
% 1.40/0.62    sK1 != sK2),
% 1.40/0.62    inference(cnf_transformation,[],[f20])).
% 1.40/0.62  fof(f20,plain,(
% 1.40/0.62    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.40/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).
% 1.40/0.62  fof(f19,plain,(
% 1.40/0.62    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.40/0.62    introduced(choice_axiom,[])).
% 1.40/0.62  fof(f17,plain,(
% 1.40/0.62    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.40/0.62    inference(flattening,[],[f16])).
% 1.40/0.62  fof(f16,plain,(
% 1.40/0.62    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.40/0.62    inference(ennf_transformation,[],[f15])).
% 1.40/0.62  fof(f15,negated_conjecture,(
% 1.40/0.62    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.40/0.62    inference(negated_conjecture,[],[f14])).
% 1.40/0.62  fof(f14,conjecture,(
% 1.40/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.40/0.62  fof(f1626,plain,(
% 1.40/0.62    sK1 = sK2),
% 1.40/0.62    inference(backward_demodulation,[],[f243,f1622])).
% 1.40/0.62  fof(f1622,plain,(
% 1.40/0.62    sK1 = k4_xboole_0(sK2,sK0)),
% 1.40/0.62    inference(forward_demodulation,[],[f1621,f1553])).
% 1.40/0.62  fof(f1553,plain,(
% 1.40/0.62    sK1 = k4_xboole_0(sK1,sK0)),
% 1.40/0.62    inference(backward_demodulation,[],[f770,f1527])).
% 1.40/0.62  fof(f1527,plain,(
% 1.40/0.62    sK0 = sK3),
% 1.40/0.62    inference(forward_demodulation,[],[f1516,f29])).
% 1.40/0.62  fof(f29,plain,(
% 1.40/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.40/0.62    inference(cnf_transformation,[],[f10])).
% 1.40/0.62  fof(f10,axiom,(
% 1.40/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.40/0.62  fof(f1516,plain,(
% 1.40/0.62    sK3 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.40/0.62    inference(backward_demodulation,[],[f1094,f1509])).
% 1.40/0.62  fof(f1509,plain,(
% 1.40/0.62    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 1.40/0.62    inference(forward_demodulation,[],[f1491,f405])).
% 1.40/0.62  fof(f405,plain,(
% 1.40/0.62    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.40/0.62    inference(forward_demodulation,[],[f372,f62])).
% 1.40/0.62  fof(f62,plain,(
% 1.40/0.62    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.40/0.62    inference(superposition,[],[f57,f28])).
% 1.40/0.62  fof(f28,plain,(
% 1.40/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.40/0.62    inference(cnf_transformation,[],[f6])).
% 1.40/0.62  fof(f6,axiom,(
% 1.40/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.40/0.62  fof(f57,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.40/0.62    inference(resolution,[],[f36,f30])).
% 1.40/0.62  fof(f30,plain,(
% 1.40/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f8])).
% 1.40/0.62  fof(f8,axiom,(
% 1.40/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.40/0.62  fof(f36,plain,(
% 1.40/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.40/0.62    inference(cnf_transformation,[],[f18])).
% 1.40/0.62  fof(f18,plain,(
% 1.40/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.40/0.62    inference(ennf_transformation,[],[f5])).
% 1.40/0.62  fof(f5,axiom,(
% 1.40/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.40/0.62  fof(f372,plain,(
% 1.40/0.62    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.40/0.62    inference(superposition,[],[f41,f55])).
% 1.40/0.62  fof(f55,plain,(
% 1.40/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.40/0.62    inference(forward_demodulation,[],[f42,f29])).
% 1.40/0.62  fof(f42,plain,(
% 1.40/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.40/0.62    inference(definition_unfolding,[],[f27,f33])).
% 1.40/0.62  fof(f33,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f13])).
% 1.40/0.62  fof(f13,axiom,(
% 1.40/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.40/0.62  fof(f27,plain,(
% 1.40/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f7])).
% 1.40/0.62  fof(f7,axiom,(
% 1.40/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.40/0.62  fof(f41,plain,(
% 1.40/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f12])).
% 1.40/0.62  fof(f12,axiom,(
% 1.40/0.62    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.40/0.62  fof(f1491,plain,(
% 1.40/0.62    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.40/0.62    inference(superposition,[],[f748,f23])).
% 1.40/0.62  fof(f23,plain,(
% 1.40/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.40/0.62    inference(cnf_transformation,[],[f20])).
% 1.40/0.62  fof(f748,plain,(
% 1.40/0.62    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))) )),
% 1.40/0.62    inference(superposition,[],[f41,f742])).
% 1.40/0.62  fof(f742,plain,(
% 1.40/0.62    sK0 = k4_xboole_0(sK0,sK2)),
% 1.40/0.62    inference(forward_demodulation,[],[f741,f57])).
% 1.40/0.62  fof(f741,plain,(
% 1.40/0.62    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 1.40/0.62    inference(forward_demodulation,[],[f733,f28])).
% 1.40/0.62  fof(f733,plain,(
% 1.40/0.62    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 1.40/0.62    inference(superposition,[],[f34,f694])).
% 1.40/0.62  fof(f694,plain,(
% 1.40/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.40/0.62    inference(forward_demodulation,[],[f635,f55])).
% 1.40/0.62  fof(f635,plain,(
% 1.40/0.62    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.40/0.62    inference(superposition,[],[f43,f243])).
% 1.40/0.62  fof(f43,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.40/0.62    inference(definition_unfolding,[],[f31,f33,f33])).
% 1.40/0.62  fof(f31,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f2])).
% 1.40/0.62  fof(f2,axiom,(
% 1.40/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.40/0.62  fof(f34,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.40/0.62    inference(cnf_transformation,[],[f9])).
% 1.40/0.62  fof(f9,axiom,(
% 1.40/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.40/0.62  fof(f1094,plain,(
% 1.40/0.62    sK3 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3))),
% 1.40/0.62    inference(forward_demodulation,[],[f1084,f29])).
% 1.40/0.62  fof(f1084,plain,(
% 1.40/0.62    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3))),
% 1.40/0.62    inference(superposition,[],[f43,f1020])).
% 1.40/0.62  fof(f1020,plain,(
% 1.40/0.62    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 1.40/0.62    inference(superposition,[],[f518,f134])).
% 1.40/0.62  fof(f134,plain,(
% 1.40/0.62    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.40/0.62    inference(forward_demodulation,[],[f133,f55])).
% 1.40/0.62  fof(f133,plain,(
% 1.40/0.62    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.40/0.62    inference(superposition,[],[f35,f124])).
% 1.40/0.62  fof(f124,plain,(
% 1.40/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.40/0.62    inference(forward_demodulation,[],[f123,f23])).
% 1.40/0.62  fof(f123,plain,(
% 1.40/0.62    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.40/0.62    inference(forward_demodulation,[],[f122,f32])).
% 1.40/0.62  fof(f32,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f1])).
% 1.40/0.62  fof(f1,axiom,(
% 1.40/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.40/0.62  fof(f122,plain,(
% 1.40/0.62    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.40/0.62    inference(forward_demodulation,[],[f117,f34])).
% 1.40/0.62  fof(f117,plain,(
% 1.40/0.62    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.40/0.62    inference(superposition,[],[f34,f104])).
% 1.40/0.62  fof(f104,plain,(
% 1.40/0.62    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.40/0.62    inference(superposition,[],[f35,f23])).
% 1.40/0.62  fof(f35,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f11])).
% 1.40/0.62  fof(f11,axiom,(
% 1.40/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.40/0.62  fof(f518,plain,(
% 1.40/0.62    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 1.40/0.62    inference(superposition,[],[f387,f32])).
% 1.40/0.62  fof(f387,plain,(
% 1.40/0.62    ( ! [X28] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X28)) = k4_xboole_0(sK3,X28)) )),
% 1.40/0.62    inference(superposition,[],[f41,f262])).
% 1.40/0.62  fof(f262,plain,(
% 1.40/0.62    sK3 = k4_xboole_0(sK3,sK1)),
% 1.40/0.62    inference(forward_demodulation,[],[f261,f57])).
% 1.40/0.62  fof(f261,plain,(
% 1.40/0.62    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 1.40/0.62    inference(forward_demodulation,[],[f255,f28])).
% 1.40/0.62  fof(f255,plain,(
% 1.40/0.62    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)),
% 1.40/0.62    inference(superposition,[],[f34,f234])).
% 1.40/0.62  fof(f234,plain,(
% 1.40/0.62    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.40/0.62    inference(resolution,[],[f45,f25])).
% 1.40/0.62  fof(f25,plain,(
% 1.40/0.62    r1_xboole_0(sK3,sK1)),
% 1.40/0.62    inference(cnf_transformation,[],[f20])).
% 1.40/0.62  fof(f45,plain,(
% 1.40/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.40/0.62    inference(definition_unfolding,[],[f37,f33])).
% 1.40/0.62  fof(f37,plain,(
% 1.40/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.40/0.62    inference(cnf_transformation,[],[f21])).
% 1.40/0.62  fof(f21,plain,(
% 1.40/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.40/0.62    inference(nnf_transformation,[],[f3])).
% 1.40/0.62  fof(f3,axiom,(
% 1.40/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.40/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.40/0.62  fof(f770,plain,(
% 1.40/0.62    sK1 = k4_xboole_0(sK1,sK3)),
% 1.40/0.62    inference(forward_demodulation,[],[f769,f57])).
% 1.40/0.62  fof(f769,plain,(
% 1.40/0.62    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 1.40/0.62    inference(forward_demodulation,[],[f761,f28])).
% 1.40/0.62  fof(f761,plain,(
% 1.40/0.62    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)),
% 1.40/0.62    inference(superposition,[],[f34,f696])).
% 1.40/0.62  fof(f696,plain,(
% 1.40/0.62    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.40/0.62    inference(forward_demodulation,[],[f637,f55])).
% 1.40/0.62  fof(f637,plain,(
% 1.40/0.62    k4_xboole_0(sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.40/0.62    inference(superposition,[],[f43,f262])).
% 1.40/0.62  fof(f1621,plain,(
% 1.40/0.62    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 1.40/0.62    inference(forward_demodulation,[],[f1610,f99])).
% 1.40/0.62  fof(f99,plain,(
% 1.40/0.62    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 1.40/0.62    inference(superposition,[],[f35,f32])).
% 1.40/0.62  fof(f1610,plain,(
% 1.40/0.62    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 1.40/0.62    inference(superposition,[],[f35,f1532])).
% 1.40/0.62  fof(f1532,plain,(
% 1.40/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 1.40/0.62    inference(backward_demodulation,[],[f23,f1527])).
% 1.40/0.62  fof(f243,plain,(
% 1.40/0.62    sK2 = k4_xboole_0(sK2,sK0)),
% 1.40/0.62    inference(forward_demodulation,[],[f242,f57])).
% 1.40/0.62  fof(f242,plain,(
% 1.40/0.62    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 1.40/0.62    inference(forward_demodulation,[],[f236,f28])).
% 1.40/0.62  fof(f236,plain,(
% 1.40/0.62    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 1.40/0.62    inference(superposition,[],[f34,f233])).
% 1.40/0.62  fof(f233,plain,(
% 1.40/0.62    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.40/0.62    inference(resolution,[],[f45,f24])).
% 1.40/0.62  fof(f24,plain,(
% 1.40/0.62    r1_xboole_0(sK2,sK0)),
% 1.40/0.62    inference(cnf_transformation,[],[f20])).
% 1.40/0.62  % SZS output end Proof for theBenchmark
% 1.40/0.62  % (10299)------------------------------
% 1.40/0.62  % (10299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.62  % (10299)Termination reason: Refutation
% 1.40/0.62  
% 1.40/0.62  % (10299)Memory used [KB]: 11513
% 1.40/0.62  % (10299)Time elapsed: 0.205 s
% 1.40/0.62  % (10299)------------------------------
% 1.40/0.62  % (10299)------------------------------
% 1.40/0.62  % (10295)Success in time 0.261 s
%------------------------------------------------------------------------------
