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
% DateTime   : Thu Dec  3 12:31:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  45 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  69 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f785,plain,(
    $false ),
    inference(resolution,[],[f772,f14])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f772,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f757])).

fof(f757,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f22,f137])).

fof(f137,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,X4)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f136,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f17,f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f136,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,X4))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f98,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f98,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X4)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f21,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f22,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f15,f18,f18])).

fof(f15,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (27103)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.44  % (27112)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (27103)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f785,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(resolution,[],[f772,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.20/0.46  fof(f772,plain,(
% 0.20/0.46    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f757])).
% 0.20/0.46  fof(f757,plain,(
% 0.20/0.46    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(superposition,[],[f22,f137])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,X4) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f136,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.46    inference(superposition,[],[f17,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,X4)) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f98,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X4) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.46    inference(superposition,[],[f21,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(superposition,[],[f23,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f20,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.46    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f19,f18])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(definition_unfolding,[],[f15,f18,f18])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (27103)------------------------------
% 0.20/0.46  % (27103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27103)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (27103)Memory used [KB]: 6652
% 0.20/0.46  % (27103)Time elapsed: 0.053 s
% 0.20/0.46  % (27103)------------------------------
% 0.20/0.46  % (27103)------------------------------
% 0.20/0.47  % (27091)Success in time 0.112 s
%------------------------------------------------------------------------------
