%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  51 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 108 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(subsumption_resolution,[],[f153,f21])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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

fof(f153,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f36,f115])).

fof(f115,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f62,f114])).

fof(f114,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) ),
    inference(forward_demodulation,[],[f98,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f98,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(superposition,[],[f38,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f33,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f62,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f23,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (5122)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.42  % (5122)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f154,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f153,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(negated_conjecture,[],[f10])).
% 0.20/0.42  fof(f10,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.42  fof(f153,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f148])).
% 0.20/0.42  fof(f148,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(superposition,[],[f36,f115])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.42    inference(backward_demodulation,[],[f62,f114])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) )),
% 0.20/0.42    inference(forward_demodulation,[],[f98,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)) )),
% 0.20/0.42    inference(superposition,[],[f38,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.42    inference(resolution,[],[f32,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    r1_tarski(sK0,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f33,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.20/0.42    inference(resolution,[],[f37,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.42    inference(definition_unfolding,[],[f23,f26])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f29,f26])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f30,f26])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (5122)------------------------------
% 0.20/0.42  % (5122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (5122)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (5122)Memory used [KB]: 10618
% 0.20/0.42  % (5122)Time elapsed: 0.008 s
% 0.20/0.42  % (5122)------------------------------
% 0.20/0.42  % (5122)------------------------------
% 0.20/0.42  % (5112)Success in time 0.066 s
%------------------------------------------------------------------------------
