%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  63 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(resolution,[],[f101,f48])).

fof(f48,plain,(
    ! [X3,X1] : sP3(X3,X1,X3) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f101,plain,(
    ! [X0] : ~ sP3(X0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f99,f75])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP3(X0,sK0,sK0) ) ),
    inference(superposition,[],[f46,f66])).

fof(f66,plain,(
    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f26,f49,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f24,f37])).

fof(f37,plain,(
    k1_xboole_0 = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f17,f36])).

fof(f17,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.54  % (30852)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (30852)Refutation not found, incomplete strategy% (30852)------------------------------
% 0.20/0.54  % (30852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30852)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30852)Memory used [KB]: 1663
% 0.20/0.54  % (30852)Time elapsed: 0.111 s
% 0.20/0.54  % (30852)------------------------------
% 0.20/0.54  % (30852)------------------------------
% 0.20/0.55  % (30856)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.55  % (30870)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (30870)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (30860)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(resolution,[],[f101,f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X3,X1] : (sP3(X3,X1,X3)) )),
% 0.20/0.56    inference(equality_resolution,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (X0 != X3 | sP3(X3,X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    ( ! [X0] : (~sP3(X0,sK0,sK0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f99,f75])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f27,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f25,f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f22,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP3(X0,sK0,sK0)) )),
% 0.20/0.56    inference(superposition,[],[f46,f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f26,f49,f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)),
% 0.20/0.56    inference(superposition,[],[f24,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    k1_xboole_0 = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.20/0.56    inference(definition_unfolding,[],[f17,f36])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.56    inference(negated_conjecture,[],[f13])).
% 0.20/0.56  fof(f13,conjecture,(
% 0.20/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_enumset1(X0,X0,X1)) | ~sP3(X3,X1,X0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.56    inference(definition_unfolding,[],[f31,f35])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (30870)------------------------------
% 0.20/0.56  % (30870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (30870)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (30870)Memory used [KB]: 1791
% 0.20/0.56  % (30870)Time elapsed: 0.126 s
% 0.20/0.56  % (30870)------------------------------
% 0.20/0.56  % (30870)------------------------------
% 0.20/0.56  % (30850)Success in time 0.198 s
%------------------------------------------------------------------------------
