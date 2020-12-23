%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  71 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :   85 ( 191 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(resolution,[],[f77,f22])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f77,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f18,f74])).

fof(f74,plain,(
    k1_xboole_0 = sK2 ),
    inference(superposition,[],[f73,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f73,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f71,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f30,f24])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f71,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    r1_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f38,f21])).

fof(f21,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK2,sK0)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK0,sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK2,sK0)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK0,X0)
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f36,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2,X0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f29,f19])).

fof(f19,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f37,f26])).

fof(f37,plain,(
    ! [X1] :
      ( r1_xboole_0(sK2,X1)
      | ~ r1_xboole_0(sK1,X1) ) ),
    inference(resolution,[],[f29,f20])).

fof(f20,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f25])).

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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f18,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (29077)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.41  % (29077)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f91,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(resolution,[],[f77,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    v1_xboole_0(k1_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    v1_xboole_0(k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.41  fof(f77,plain,(
% 0.20/0.41    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.41    inference(backward_demodulation,[],[f18,f74])).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    k1_xboole_0 = sK2),
% 0.20/0.41    inference(superposition,[],[f73,f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)),
% 0.20/0.41    inference(forward_demodulation,[],[f71,f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.41    inference(forward_demodulation,[],[f30,f24])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f23,f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.41  fof(f71,plain,(
% 0.20/0.41    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),
% 0.20/0.41    inference(resolution,[],[f32,f44])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    r1_xboole_0(sK2,sK2)),
% 0.20/0.41    inference(resolution,[],[f39,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    r1_xboole_0(sK1,sK2)),
% 0.20/0.41    inference(resolution,[],[f38,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    r1_xboole_0(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 0.20/0.41    inference(flattening,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.41    inference(negated_conjecture,[],[f8])).
% 0.20/0.41  fof(f8,conjecture,(
% 0.20/0.41    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(sK0,X0) | r1_xboole_0(X0,sK2)) )),
% 0.20/0.41    inference(resolution,[],[f36,f26])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X0] : (r1_xboole_0(sK2,X0) | ~r1_xboole_0(sK0,X0)) )),
% 0.20/0.41    inference(resolution,[],[f29,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    r1_tarski(sK2,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(flattening,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(X0,sK2)) )),
% 0.20/0.41    inference(resolution,[],[f37,f26])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ( ! [X1] : (r1_xboole_0(sK2,X1) | ~r1_xboole_0(sK1,X1)) )),
% 0.20/0.41    inference(resolution,[],[f29,f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    r1_tarski(sK2,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f27,f25])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.41    inference(nnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ~v1_xboole_0(sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (29077)------------------------------
% 0.20/0.41  % (29077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (29077)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (29077)Memory used [KB]: 6140
% 0.20/0.41  % (29077)Time elapsed: 0.005 s
% 0.20/0.41  % (29077)------------------------------
% 0.20/0.41  % (29077)------------------------------
% 0.20/0.41  % (29074)Success in time 0.057 s
%------------------------------------------------------------------------------
