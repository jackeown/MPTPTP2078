%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 (  83 expanded)
%              Number of equality atoms :   35 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f41,f60])).

fof(f60,plain,(
    ! [X0] : k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ),
    inference(subsumption_resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X1] : r2_hidden(X1,k9_setfam_1(X1)) ),
    inference(forward_demodulation,[],[f52,f44])).

fof(f44,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f52,plain,(
    ! [X1] : r2_hidden(X1,k9_setfam_1(k3_tarski(k1_enumset1(X1,X1,X1)))) ),
    inference(resolution,[],[f46,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(X0,k9_setfam_1(k3_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f28,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_setfam_1(X0))
      | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ) ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f31,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f41,plain,(
    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f25,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).

fof(f18,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:54:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (21318)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.43  % (21318)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f61])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    sK0 != sK0),
% 0.21/0.43    inference(superposition,[],[f41,f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0] : (k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f58,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X1] : (r2_hidden(X1,k9_setfam_1(X1))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f52,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f34,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f35,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    inference(rectify,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X1] : (r2_hidden(X1,k9_setfam_1(k3_tarski(k1_enumset1(X1,X1,X1))))) )),
% 0.21/0.43    inference(resolution,[],[f46,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(X0,k9_setfam_1(k3_tarski(X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f28,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f37,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f30,f36])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k9_setfam_1(X0)) | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.21/0.43    inference(superposition,[],[f57,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f27,f26])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f31,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(rectify,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.21/0.43    inference(definition_unfolding,[],[f25,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.21/0.43    inference(negated_conjecture,[],[f12])).
% 0.21/0.43  fof(f12,conjecture,(
% 0.21/0.43    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (21318)------------------------------
% 0.21/0.43  % (21318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (21318)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (21318)Memory used [KB]: 1663
% 0.21/0.43  % (21318)Time elapsed: 0.006 s
% 0.21/0.43  % (21318)------------------------------
% 0.21/0.43  % (21318)------------------------------
% 0.21/0.43  % (21302)Success in time 0.077 s
%------------------------------------------------------------------------------
