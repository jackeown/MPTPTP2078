%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  65 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 107 expanded)
%              Number of equality atoms :   27 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(subsumption_resolution,[],[f40,f29])).

fof(f29,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f17,f28,f21,f28])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f40,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f35,f16])).

fof(f16,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k2_enumset1(X0,X0,X0,sK0),sK1) ) ),
    inference(resolution,[],[f32,f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:53:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.41  % (30798)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.41  % (30798)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f40,f29])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.41    inference(definition_unfolding,[],[f17,f28,f21,f28])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f18,f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f20,f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.41    inference(negated_conjecture,[],[f8])).
% 0.20/0.41  fof(f8,conjecture,(
% 0.20/0.41    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.41    inference(superposition,[],[f39,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.20/0.41    inference(resolution,[],[f36,f31])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.41    inference(definition_unfolding,[],[f22,f21])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.41    inference(resolution,[],[f35,f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    r2_hidden(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(X0,X0,X0,sK0),sK1)) )),
% 0.20/0.41    inference(resolution,[],[f32,f16])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f26,f27])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.41    inference(flattening,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.41    inference(nnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (30798)------------------------------
% 0.20/0.41  % (30798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (30798)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (30798)Memory used [KB]: 1663
% 0.20/0.41  % (30798)Time elapsed: 0.005 s
% 0.20/0.41  % (30798)------------------------------
% 0.20/0.41  % (30798)------------------------------
% 0.20/0.42  % (30784)Success in time 0.066 s
%------------------------------------------------------------------------------
