%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:45 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   38 (  54 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 124 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(global_subsumption,[],[f55,f89])).

fof(f89,plain,(
    r1_tarski(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f23,f74])).

fof(f74,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f69,f29])).

fof(f29,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(resolution,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) ),
    inference(forward_demodulation,[],[f58,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[],[f25,f30])).

fof(f30,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f52,f17])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,k4_xboole_0(X0,sK2))
      | ~ r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f51,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f26,f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : run_vampire %s %d
% 0.11/0.30  % Computer   : n001.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 11:38:59 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.37  % (2725)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.16/0.37  % (2726)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.16/0.37  % (2727)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.16/0.38  % (2726)Refutation found. Thanks to Tanya!
% 0.16/0.38  % SZS status Theorem for theBenchmark
% 0.16/0.38  % SZS output start Proof for theBenchmark
% 0.16/0.38  fof(f91,plain,(
% 0.16/0.38    $false),
% 0.16/0.38    inference(global_subsumption,[],[f55,f89])).
% 0.16/0.38  fof(f89,plain,(
% 0.16/0.38    r1_tarski(sK0,sK1)),
% 0.16/0.38    inference(trivial_inequality_removal,[],[f85])).
% 0.16/0.38  fof(f85,plain,(
% 0.16/0.38    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1)),
% 0.16/0.38    inference(superposition,[],[f23,f74])).
% 0.16/0.38  fof(f74,plain,(
% 0.16/0.38    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.16/0.38    inference(superposition,[],[f69,f29])).
% 0.16/0.38  fof(f29,plain,(
% 0.16/0.38    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1) )),
% 0.16/0.38    inference(resolution,[],[f22,f21])).
% 0.16/0.38  fof(f21,plain,(
% 0.16/0.38    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.16/0.38    inference(cnf_transformation,[],[f4])).
% 0.16/0.38  fof(f4,axiom,(
% 0.16/0.38    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.16/0.38  fof(f22,plain,(
% 0.16/0.38    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.16/0.38    inference(cnf_transformation,[],[f11])).
% 0.16/0.38  fof(f11,plain,(
% 0.16/0.38    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.16/0.38    inference(ennf_transformation,[],[f2])).
% 0.16/0.38  fof(f2,axiom,(
% 0.16/0.38    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.16/0.38  fof(f69,plain,(
% 0.16/0.38    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0))) )),
% 0.16/0.38    inference(forward_demodulation,[],[f58,f31])).
% 0.16/0.38  fof(f31,plain,(
% 0.16/0.38    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.16/0.38    inference(resolution,[],[f24,f19])).
% 0.16/0.38  fof(f19,plain,(
% 0.16/0.38    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.16/0.38    inference(cnf_transformation,[],[f3])).
% 0.16/0.38  fof(f3,axiom,(
% 0.16/0.38    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.16/0.38  fof(f24,plain,(
% 0.16/0.38    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.16/0.38    inference(cnf_transformation,[],[f16])).
% 0.16/0.38  fof(f16,plain,(
% 0.16/0.38    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.16/0.38    inference(nnf_transformation,[],[f1])).
% 0.16/0.38  fof(f1,axiom,(
% 0.16/0.38    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.16/0.38  fof(f58,plain,(
% 0.16/0.38    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0))) )),
% 0.16/0.38    inference(superposition,[],[f25,f30])).
% 0.16/0.38  fof(f30,plain,(
% 0.16/0.38    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.16/0.38    inference(resolution,[],[f24,f17])).
% 0.16/0.38  fof(f17,plain,(
% 0.16/0.38    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.16/0.38    inference(cnf_transformation,[],[f15])).
% 0.16/0.38  fof(f15,plain,(
% 0.16/0.38    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.16/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).
% 0.16/0.38  fof(f14,plain,(
% 0.16/0.38    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.16/0.38    introduced(choice_axiom,[])).
% 0.16/0.38  fof(f10,plain,(
% 0.16/0.38    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.16/0.38    inference(ennf_transformation,[],[f9])).
% 0.16/0.38  fof(f9,negated_conjecture,(
% 0.16/0.38    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.16/0.38    inference(negated_conjecture,[],[f8])).
% 0.16/0.38  fof(f8,conjecture,(
% 0.16/0.38    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.16/0.38  fof(f25,plain,(
% 0.16/0.38    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.16/0.38    inference(cnf_transformation,[],[f5])).
% 0.16/0.38  fof(f5,axiom,(
% 0.16/0.38    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.16/0.38  fof(f23,plain,(
% 0.16/0.38    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.16/0.38    inference(cnf_transformation,[],[f16])).
% 0.16/0.38  fof(f55,plain,(
% 0.16/0.38    ~r1_tarski(sK0,sK1)),
% 0.16/0.38    inference(resolution,[],[f52,f17])).
% 0.16/0.38  fof(f52,plain,(
% 0.16/0.38    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(X0,sK2)) | ~r1_tarski(sK0,sK1)) )),
% 0.16/0.38    inference(resolution,[],[f51,f20])).
% 0.16/0.38  fof(f20,plain,(
% 0.16/0.38    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.16/0.38    inference(cnf_transformation,[],[f7])).
% 0.16/0.38  fof(f7,axiom,(
% 0.16/0.38    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.16/0.38  fof(f51,plain,(
% 0.16/0.38    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~r1_tarski(sK0,X0) | ~r1_tarski(sK0,sK1)) )),
% 0.16/0.38    inference(resolution,[],[f26,f18])).
% 0.16/0.38  fof(f18,plain,(
% 0.16/0.38    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.16/0.38    inference(cnf_transformation,[],[f15])).
% 0.16/0.38  fof(f26,plain,(
% 0.16/0.38    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.16/0.38    inference(cnf_transformation,[],[f13])).
% 0.16/0.38  fof(f13,plain,(
% 0.16/0.38    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.16/0.38    inference(flattening,[],[f12])).
% 0.16/0.38  fof(f12,plain,(
% 0.16/0.38    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.16/0.38    inference(ennf_transformation,[],[f6])).
% 0.16/0.38  fof(f6,axiom,(
% 0.16/0.38    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.16/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.16/0.38  % SZS output end Proof for theBenchmark
% 0.16/0.38  % (2726)------------------------------
% 0.16/0.38  % (2726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.38  % (2726)Termination reason: Refutation
% 0.16/0.38  
% 0.16/0.38  % (2726)Memory used [KB]: 6140
% 0.16/0.38  % (2726)Time elapsed: 0.006 s
% 0.16/0.38  % (2726)------------------------------
% 0.16/0.38  % (2726)------------------------------
% 0.16/0.38  % (2721)Success in time 0.061 s
%------------------------------------------------------------------------------
