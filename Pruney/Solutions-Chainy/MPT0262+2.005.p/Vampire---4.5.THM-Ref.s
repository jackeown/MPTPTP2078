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
% DateTime   : Thu Dec  3 12:40:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  53 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 131 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(subsumption_resolution,[],[f53,f14])).

fof(f14,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ~ r2_hidden(sK2,sK1)
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ~ r2_hidden(sK2,sK1)
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
      & ~ r2_hidden(X2,X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f53,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f47,f15])).

fof(f15,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f41,f23])).

fof(f23,plain,(
    ~ r1_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)),sK1) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f16,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),X1)) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),X3)
      | r2_hidden(X2,X3)
      | r2_hidden(X1,X3)
      | r2_hidden(X0,X3) ) ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X3)
      | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),X3)
      | r2_hidden(X2,X3)
      | r2_hidden(X1,X3) ) ),
    inference(resolution,[],[f33,f19])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k1_tarski(X2))),X3)
      | ~ r1_xboole_0(X0,X3)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f32,f19])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(forward_demodulation,[],[f21,f20])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:04:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.48  % (15434)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (15434)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f53,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_tarski(sK0,sK2),sK1) & ~r2_hidden(sK2,sK1) & ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1)) => (~r1_xboole_0(k2_tarski(sK0,sK2),sK1) & ~r2_hidden(sK2,sK1) & ~r2_hidden(sK0,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f47,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ~r2_hidden(sK2,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    r2_hidden(sK2,sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f41,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)),sK1)),
% 0.22/0.48    inference(definition_unfolding,[],[f16,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2) | r2_hidden(X0,X2)) )),
% 0.22/0.48    inference(superposition,[],[f35,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),X1))) )),
% 0.22/0.48    inference(superposition,[],[f20,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f17,f18])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),X3) | r2_hidden(X2,X3) | r2_hidden(X1,X3) | r2_hidden(X0,X3)) )),
% 0.22/0.48    inference(resolution,[],[f34,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X3) | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),X3) | r2_hidden(X2,X3) | r2_hidden(X1,X3)) )),
% 0.22/0.48    inference(resolution,[],[f33,f19])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X1,X3) | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k1_tarski(X2))),X3) | ~r1_xboole_0(X0,X3) | r2_hidden(X2,X3)) )),
% 0.22/0.48    inference(resolution,[],[f32,f19])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f21,f20])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) | ~r1_xboole_0(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) | ~r1_xboole_0(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) | (~r1_xboole_0(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (15434)------------------------------
% 0.22/0.48  % (15434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15434)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (15434)Memory used [KB]: 1663
% 0.22/0.48  % (15434)Time elapsed: 0.030 s
% 0.22/0.48  % (15434)------------------------------
% 0.22/0.48  % (15434)------------------------------
% 0.22/0.48  % (15421)Success in time 0.113 s
%------------------------------------------------------------------------------
