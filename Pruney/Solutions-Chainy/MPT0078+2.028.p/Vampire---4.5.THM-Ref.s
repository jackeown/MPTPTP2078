%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  51 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 149 expanded)
%              Number of equality atoms :   32 (  82 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(subsumption_resolution,[],[f30,f14])).

fof(f14,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f30,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f29,f24])).

fof(f24,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f16,f19])).

fof(f19,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f12,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f12,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f29,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f27,f22])).

fof(f22,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f21,f15])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f21,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f15,f11])).

fof(f11,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f16,f20])).

fof(f20,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f13,f17])).

fof(f13,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (2097)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.42  % (2097)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f30,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    sK0 != sK2),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    sK0 = sK2),
% 0.21/0.42    inference(forward_demodulation,[],[f29,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.42    inference(superposition,[],[f16,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(resolution,[],[f12,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.42    inference(forward_demodulation,[],[f27,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(forward_demodulation,[],[f21,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.21/0.42    inference(superposition,[],[f15,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 0.21/0.42    inference(superposition,[],[f16,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.21/0.42    inference(resolution,[],[f13,f17])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    r1_xboole_0(sK2,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2097)------------------------------
% 0.21/0.42  % (2097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2097)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2097)Memory used [KB]: 1535
% 0.21/0.42  % (2097)Time elapsed: 0.004 s
% 0.21/0.42  % (2097)------------------------------
% 0.21/0.42  % (2097)------------------------------
% 0.21/0.42  % (2092)Success in time 0.065 s
%------------------------------------------------------------------------------
