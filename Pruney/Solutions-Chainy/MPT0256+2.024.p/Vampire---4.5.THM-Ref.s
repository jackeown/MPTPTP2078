%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:02 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 (  53 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  81 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f15])).

fof(f15,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r2_hidden(sK1,sK0)
    & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) )
   => ( ~ r2_hidden(sK1,sK0)
      & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f32,plain,(
    r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f29,f31])).

fof(f31,plain,(
    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f17,f27])).

fof(f27,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f14,f26,f26])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (6905)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.13/0.40  % (6905)Refutation found. Thanks to Tanya!
% 0.13/0.40  % SZS status Theorem for theBenchmark
% 0.13/0.40  % SZS output start Proof for theBenchmark
% 0.13/0.40  fof(f33,plain,(
% 0.13/0.40    $false),
% 0.13/0.40    inference(subsumption_resolution,[],[f32,f15])).
% 0.13/0.40  fof(f15,plain,(
% 0.13/0.40    ~r2_hidden(sK1,sK0)),
% 0.13/0.40    inference(cnf_transformation,[],[f11])).
% 0.13/0.40  fof(f11,plain,(
% 0.13/0.40    ~r2_hidden(sK1,sK0) & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 0.13/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.13/0.40  fof(f10,plain,(
% 0.13/0.40    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))) => (~r2_hidden(sK1,sK0) & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)))),
% 0.13/0.40    introduced(choice_axiom,[])).
% 0.13/0.40  fof(f9,plain,(
% 0.13/0.40    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)))),
% 0.13/0.40    inference(ennf_transformation,[],[f8])).
% 0.13/0.40  fof(f8,negated_conjecture,(
% 0.13/0.40    ~! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.13/0.40    inference(negated_conjecture,[],[f7])).
% 0.13/0.40  fof(f7,conjecture,(
% 0.13/0.40    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 0.13/0.40  fof(f32,plain,(
% 0.13/0.40    r2_hidden(sK1,sK0)),
% 0.13/0.40    inference(resolution,[],[f29,f31])).
% 0.13/0.40  fof(f31,plain,(
% 0.13/0.40    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.13/0.40    inference(superposition,[],[f17,f27])).
% 0.13/0.40  fof(f27,plain,(
% 0.13/0.40    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.13/0.40    inference(definition_unfolding,[],[f14,f26,f26])).
% 0.13/0.40  fof(f26,plain,(
% 0.13/0.40    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.13/0.40    inference(definition_unfolding,[],[f16,f25])).
% 0.13/0.40  fof(f25,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.13/0.40    inference(definition_unfolding,[],[f18,f24])).
% 0.13/0.40  fof(f24,plain,(
% 0.13/0.40    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.13/0.40    inference(definition_unfolding,[],[f19,f23])).
% 0.13/0.40  fof(f23,plain,(
% 0.13/0.40    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f5])).
% 0.13/0.40  fof(f5,axiom,(
% 0.13/0.40    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.13/0.40  fof(f19,plain,(
% 0.13/0.40    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f4])).
% 0.13/0.40  fof(f4,axiom,(
% 0.13/0.40    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.13/0.40  fof(f18,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f3])).
% 0.13/0.40  fof(f3,axiom,(
% 0.13/0.40    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.13/0.40  fof(f16,plain,(
% 0.13/0.40    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f2])).
% 0.13/0.40  fof(f2,axiom,(
% 0.13/0.40    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.13/0.40  fof(f14,plain,(
% 0.13/0.40    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 0.13/0.40    inference(cnf_transformation,[],[f11])).
% 0.13/0.40  fof(f17,plain,(
% 0.13/0.40    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f1])).
% 0.13/0.40  fof(f1,axiom,(
% 0.13/0.40    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.13/0.40  fof(f29,plain,(
% 0.13/0.40    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.13/0.40    inference(definition_unfolding,[],[f21,f25])).
% 0.13/0.40  fof(f21,plain,(
% 0.13/0.40    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f13])).
% 0.13/0.40  fof(f13,plain,(
% 0.13/0.40    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.13/0.40    inference(flattening,[],[f12])).
% 0.13/0.40  fof(f12,plain,(
% 0.13/0.40    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.13/0.40    inference(nnf_transformation,[],[f6])).
% 0.13/0.40  fof(f6,axiom,(
% 0.13/0.40    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.13/0.40  % SZS output end Proof for theBenchmark
% 0.13/0.40  % (6905)------------------------------
% 0.13/0.40  % (6905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.40  % (6905)Termination reason: Refutation
% 0.13/0.40  
% 0.13/0.40  % (6905)Memory used [KB]: 1535
% 0.13/0.40  % (6905)Time elapsed: 0.003 s
% 0.13/0.40  % (6905)------------------------------
% 0.13/0.40  % (6905)------------------------------
% 0.13/0.41  % (6887)Success in time 0.05 s
%------------------------------------------------------------------------------
