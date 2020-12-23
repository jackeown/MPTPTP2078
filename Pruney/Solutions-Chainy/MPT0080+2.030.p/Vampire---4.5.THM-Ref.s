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
% DateTime   : Thu Dec  3 12:31:03 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 183 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :   27
%              Number of atoms          :   99 ( 306 expanded)
%              Number of equality atoms :   47 ( 152 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1577,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1564,f20])).

fof(f20,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1564,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f623,f1552])).

fof(f1552,plain,(
    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1551,f69])).

fof(f69,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f66,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f58,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f25,f42])).

fof(f42,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1551,plain,(
    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1538,f23])).

fof(f1538,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f25,f1519])).

fof(f1519,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f1515,f29])).

fof(f1515,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f1415,f21])).

fof(f1415,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X5,sK1)) ),
    inference(trivial_inequality_removal,[],[f1403])).

fof(f1403,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X5,sK1)) ) ),
    inference(superposition,[],[f511,f1340])).

fof(f1340,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(X1,sK1))) ),
    inference(forward_demodulation,[],[f1327,f23])).

fof(f1327,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X1,sK1),sK2)) ),
    inference(superposition,[],[f997,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f997,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(X0,sK1)),sK2) ),
    inference(resolution,[],[f990,f29])).

fof(f990,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(sK0,k2_xboole_0(X1,sK1)),sK2) ),
    inference(forward_demodulation,[],[f989,f30])).

fof(f989,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f977])).

fof(f977,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2) ) ),
    inference(superposition,[],[f511,f843])).

fof(f843,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f785,f29])).

fof(f785,plain,(
    ! [X16] : r1_tarski(k4_xboole_0(sK0,X16),k2_xboole_0(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f774])).

fof(f774,plain,(
    ! [X16] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,X16),k2_xboole_0(sK1,sK2)) ) ),
    inference(superposition,[],[f511,f562])).

fof(f562,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f549,f23])).

fof(f549,plain,(
    ! [X24] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X24)) ),
    inference(forward_demodulation,[],[f495,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f41,f66])).

fof(f41,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f22,f23])).

fof(f495,plain,(
    ! [X24] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X24)) = k4_xboole_0(k1_xboole_0,X24) ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f511,plain,(
    ! [X10,X11,X9] :
      ( k1_xboole_0 != k4_xboole_0(X9,k2_xboole_0(X10,X11))
      | r1_tarski(k4_xboole_0(X9,X10),X11) ) ),
    inference(superposition,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f623,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f612,f23])).

fof(f612,plain,(
    ! [X1] : r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) ),
    inference(trivial_inequality_removal,[],[f604])).

fof(f604,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) ) ),
    inference(superposition,[],[f28,f550])).

fof(f550,plain,(
    ! [X25] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X25)) ),
    inference(forward_demodulation,[],[f496,f71])).

fof(f496,plain,(
    ! [X25] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X25)) = k4_xboole_0(k1_xboole_0,X25) ),
    inference(superposition,[],[f30,f178])).

fof(f178,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n004.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:27:08 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.41  % (29794)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.44  % (29786)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.44  % (29794)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f1577,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(subsumption_resolution,[],[f1564,f20])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ~r1_tarski(sK0,sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.19/0.44    inference(flattening,[],[f12])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.19/0.44    inference(ennf_transformation,[],[f10])).
% 0.19/0.44  fof(f10,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.19/0.44    inference(negated_conjecture,[],[f9])).
% 0.19/0.44  fof(f9,conjecture,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.19/0.44  fof(f1564,plain,(
% 0.19/0.44    r1_tarski(sK0,sK1)),
% 0.19/0.44    inference(superposition,[],[f623,f1552])).
% 0.19/0.44  fof(f1552,plain,(
% 0.19/0.44    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.19/0.44    inference(forward_demodulation,[],[f1551,f69])).
% 0.19/0.44  fof(f69,plain,(
% 0.19/0.44    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.19/0.44    inference(superposition,[],[f66,f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.44  fof(f66,plain,(
% 0.19/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.44    inference(forward_demodulation,[],[f58,f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.44    inference(rectify,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.19/0.44  fof(f58,plain,(
% 0.19/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.44    inference(superposition,[],[f25,f42])).
% 0.19/0.44  fof(f42,plain,(
% 0.19/0.44    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 0.19/0.44    inference(resolution,[],[f29,f33])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.19/0.44    inference(superposition,[],[f22,f21])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,axiom,(
% 0.19/0.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.19/0.44    inference(nnf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.19/0.44  fof(f1551,plain,(
% 0.19/0.44    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.19/0.44    inference(forward_demodulation,[],[f1538,f23])).
% 0.19/0.44  fof(f1538,plain,(
% 0.19/0.44    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.19/0.44    inference(superposition,[],[f25,f1519])).
% 0.19/0.44  fof(f1519,plain,(
% 0.19/0.44    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.19/0.44    inference(resolution,[],[f1515,f29])).
% 0.19/0.44  fof(f1515,plain,(
% 0.19/0.44    r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.19/0.44    inference(superposition,[],[f1415,f21])).
% 0.19/0.44  fof(f1415,plain,(
% 0.19/0.44    ( ! [X5] : (r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X5,sK1))) )),
% 0.19/0.44    inference(trivial_inequality_removal,[],[f1403])).
% 0.19/0.44  fof(f1403,plain,(
% 0.19/0.44    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X5,sK1))) )),
% 0.19/0.44    inference(superposition,[],[f511,f1340])).
% 0.19/0.44  fof(f1340,plain,(
% 0.19/0.44    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(X1,sK1)))) )),
% 0.19/0.44    inference(forward_demodulation,[],[f1327,f23])).
% 0.19/0.44  fof(f1327,plain,(
% 0.19/0.44    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X1,sK1),sK2))) )),
% 0.19/0.44    inference(superposition,[],[f997,f30])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.19/0.44  fof(f997,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(X0,sK1)),sK2)) )),
% 0.19/0.44    inference(resolution,[],[f990,f29])).
% 0.19/0.44  fof(f990,plain,(
% 0.19/0.44    ( ! [X1] : (r1_tarski(k4_xboole_0(sK0,k2_xboole_0(X1,sK1)),sK2)) )),
% 0.19/0.44    inference(forward_demodulation,[],[f989,f30])).
% 0.19/0.44  fof(f989,plain,(
% 0.19/0.44    ( ! [X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2)) )),
% 0.19/0.44    inference(trivial_inequality_removal,[],[f977])).
% 0.19/0.44  fof(f977,plain,(
% 0.19/0.44    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2)) )),
% 0.19/0.44    inference(superposition,[],[f511,f843])).
% 0.19/0.44  fof(f843,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(sK1,sK2))) )),
% 0.19/0.44    inference(resolution,[],[f785,f29])).
% 0.19/0.44  fof(f785,plain,(
% 0.19/0.44    ( ! [X16] : (r1_tarski(k4_xboole_0(sK0,X16),k2_xboole_0(sK1,sK2))) )),
% 0.19/0.44    inference(trivial_inequality_removal,[],[f774])).
% 0.19/0.44  fof(f774,plain,(
% 0.19/0.44    ( ! [X16] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,X16),k2_xboole_0(sK1,sK2))) )),
% 0.19/0.44    inference(superposition,[],[f511,f562])).
% 0.19/0.44  fof(f562,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2)))) )),
% 0.19/0.44    inference(superposition,[],[f549,f23])).
% 0.19/0.44  fof(f549,plain,(
% 0.19/0.44    ( ! [X24] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X24))) )),
% 0.19/0.44    inference(forward_demodulation,[],[f495,f71])).
% 0.19/0.44  fof(f71,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.44    inference(superposition,[],[f41,f66])).
% 0.19/0.44  fof(f41,plain,(
% 0.19/0.44    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 0.19/0.44    inference(resolution,[],[f29,f34])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.19/0.44    inference(superposition,[],[f22,f23])).
% 0.19/0.44  fof(f495,plain,(
% 0.19/0.44    ( ! [X24] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X24)) = k4_xboole_0(k1_xboole_0,X24)) )),
% 0.19/0.44    inference(superposition,[],[f30,f39])).
% 0.19/0.44  fof(f39,plain,(
% 0.19/0.44    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.19/0.44    inference(resolution,[],[f29,f18])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  fof(f511,plain,(
% 0.19/0.44    ( ! [X10,X11,X9] : (k1_xboole_0 != k4_xboole_0(X9,k2_xboole_0(X10,X11)) | r1_tarski(k4_xboole_0(X9,X10),X11)) )),
% 0.19/0.44    inference(superposition,[],[f28,f30])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f623,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK2)))) )),
% 0.19/0.44    inference(superposition,[],[f612,f23])).
% 0.19/0.44  fof(f612,plain,(
% 0.19/0.44    ( ! [X1] : (r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X1))) )),
% 0.19/0.44    inference(trivial_inequality_removal,[],[f604])).
% 0.19/0.44  fof(f604,plain,(
% 0.19/0.44    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X1))) )),
% 0.19/0.44    inference(superposition,[],[f28,f550])).
% 0.19/0.44  fof(f550,plain,(
% 0.19/0.44    ( ! [X25] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X25))) )),
% 0.19/0.44    inference(forward_demodulation,[],[f496,f71])).
% 0.19/0.44  fof(f496,plain,(
% 0.19/0.44    ( ! [X25] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X25)) = k4_xboole_0(k1_xboole_0,X25)) )),
% 0.19/0.44    inference(superposition,[],[f30,f178])).
% 0.19/0.44  fof(f178,plain,(
% 0.19/0.44    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.19/0.44    inference(resolution,[],[f32,f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    r1_xboole_0(sK0,sK2)),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(definition_unfolding,[],[f26,f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.44    inference(nnf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (29794)------------------------------
% 0.19/0.44  % (29794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (29794)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (29794)Memory used [KB]: 2302
% 0.19/0.44  % (29794)Time elapsed: 0.034 s
% 0.19/0.44  % (29794)------------------------------
% 0.19/0.44  % (29794)------------------------------
% 0.19/0.44  % (29781)Success in time 0.107 s
%------------------------------------------------------------------------------
