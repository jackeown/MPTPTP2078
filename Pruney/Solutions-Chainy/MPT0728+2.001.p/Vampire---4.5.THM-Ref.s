%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:08 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   38 (  70 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  95 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f72,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f55,f56])).

fof(f56,plain,(
    sK0 = k2_xboole_0(sK0,k2_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f39,f48])).

fof(f48,plain,(
    sK0 = k4_xboole_0(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k2_xboole_0(X1,k2_tarski(X0,X0)),k2_tarski(X0,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f29,f30,f30])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f41,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f25,f32,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f32,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f16,f31])).

fof(f31,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f20,f30])).

fof(f20,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f16,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f39,plain,(
    k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = k4_xboole_0(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f55,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,X0)),sK0) ),
    inference(forward_demodulation,[],[f50,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f50,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k2_tarski(sK0,X0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f41,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (24625)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (24648)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.11/0.52  % (24625)Refutation found. Thanks to Tanya!
% 1.11/0.52  % SZS status Theorem for theBenchmark
% 1.11/0.52  % (24633)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.11/0.52  % SZS output start Proof for theBenchmark
% 1.11/0.52  fof(f78,plain,(
% 1.11/0.52    $false),
% 1.11/0.52    inference(resolution,[],[f72,f36])).
% 1.11/0.52  fof(f36,plain,(
% 1.11/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.11/0.52    inference(equality_resolution,[],[f23])).
% 1.11/0.52  fof(f23,plain,(
% 1.11/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.11/0.52    inference(cnf_transformation,[],[f3])).
% 1.11/0.52  fof(f3,axiom,(
% 1.11/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.11/0.52  fof(f72,plain,(
% 1.11/0.52    ~r1_tarski(sK0,sK0)),
% 1.11/0.52    inference(superposition,[],[f55,f56])).
% 1.11/0.52  fof(f56,plain,(
% 1.11/0.52    sK0 = k2_xboole_0(sK0,k2_tarski(sK0,sK0))),
% 1.11/0.52    inference(backward_demodulation,[],[f39,f48])).
% 1.11/0.52  fof(f48,plain,(
% 1.11/0.52    sK0 = k4_xboole_0(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 1.11/0.52    inference(unit_resulting_resolution,[],[f41,f35])).
% 1.11/0.52  fof(f35,plain,(
% 1.11/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k2_xboole_0(X1,k2_tarski(X0,X0)),k2_tarski(X0,X0)) = X1) )),
% 1.11/0.52    inference(definition_unfolding,[],[f29,f30,f30])).
% 1.11/0.52  fof(f30,plain,(
% 1.11/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.11/0.52    inference(cnf_transformation,[],[f5])).
% 1.11/0.52  fof(f5,axiom,(
% 1.11/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.11/0.52  fof(f29,plain,(
% 1.11/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1) )),
% 1.11/0.52    inference(cnf_transformation,[],[f15])).
% 1.11/0.52  fof(f15,plain,(
% 1.11/0.52    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | r2_hidden(X0,X1))),
% 1.11/0.52    inference(ennf_transformation,[],[f6])).
% 1.11/0.52  fof(f6,axiom,(
% 1.11/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 1.11/0.52  fof(f41,plain,(
% 1.11/0.52    ~r2_hidden(sK0,sK0)),
% 1.11/0.52    inference(unit_resulting_resolution,[],[f25,f32,f17])).
% 1.11/0.52  fof(f17,plain,(
% 1.11/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.11/0.52    inference(cnf_transformation,[],[f13])).
% 1.11/0.52  fof(f13,plain,(
% 1.11/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.11/0.52    inference(ennf_transformation,[],[f2])).
% 1.11/0.52  fof(f2,axiom,(
% 1.11/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.11/0.52  fof(f32,plain,(
% 1.11/0.52    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 1.11/0.52    inference(definition_unfolding,[],[f16,f31])).
% 1.11/0.52  fof(f31,plain,(
% 1.11/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 1.11/0.52    inference(definition_unfolding,[],[f20,f30])).
% 1.11/0.52  fof(f20,plain,(
% 1.11/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.11/0.52    inference(cnf_transformation,[],[f9])).
% 1.11/0.52  fof(f9,axiom,(
% 1.11/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.11/0.52  fof(f16,plain,(
% 1.11/0.52    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 1.11/0.52    inference(cnf_transformation,[],[f12])).
% 1.11/0.52  fof(f12,plain,(
% 1.11/0.52    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0))),
% 1.11/0.52    inference(ennf_transformation,[],[f11])).
% 1.11/0.52  fof(f11,negated_conjecture,(
% 1.11/0.52    ~! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.11/0.52    inference(negated_conjecture,[],[f10])).
% 1.11/0.52  fof(f10,conjecture,(
% 1.11/0.52    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.11/0.52  fof(f25,plain,(
% 1.11/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.11/0.52    inference(cnf_transformation,[],[f4])).
% 1.11/0.52  fof(f4,axiom,(
% 1.11/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.11/0.52  fof(f39,plain,(
% 1.11/0.52    k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = k4_xboole_0(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 1.11/0.52    inference(unit_resulting_resolution,[],[f32,f34])).
% 1.11/0.52  fof(f34,plain,(
% 1.11/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0) )),
% 1.11/0.52    inference(definition_unfolding,[],[f27,f30])).
% 1.11/0.52  fof(f27,plain,(
% 1.11/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.11/0.52    inference(cnf_transformation,[],[f8])).
% 1.11/0.52  fof(f8,axiom,(
% 1.11/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.11/0.52  fof(f55,plain,(
% 1.11/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,X0)),sK0)) )),
% 1.11/0.52    inference(forward_demodulation,[],[f50,f26])).
% 1.11/0.52  fof(f26,plain,(
% 1.11/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.11/0.52    inference(cnf_transformation,[],[f1])).
% 1.11/0.52  fof(f1,axiom,(
% 1.11/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.11/0.52  fof(f50,plain,(
% 1.11/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(k2_tarski(sK0,X0),sK0),sK0)) )),
% 1.11/0.52    inference(unit_resulting_resolution,[],[f41,f21])).
% 1.11/0.52  fof(f21,plain,(
% 1.11/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) | r2_hidden(X0,X2)) )),
% 1.11/0.52    inference(cnf_transformation,[],[f14])).
% 1.11/0.52  fof(f14,plain,(
% 1.11/0.52    ! [X0,X1,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 1.11/0.52    inference(ennf_transformation,[],[f7])).
% 1.11/0.52  fof(f7,axiom,(
% 1.11/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.11/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 1.11/0.52  % SZS output end Proof for theBenchmark
% 1.11/0.52  % (24625)------------------------------
% 1.11/0.52  % (24625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.11/0.52  % (24625)Termination reason: Refutation
% 1.11/0.52  
% 1.11/0.52  % (24625)Memory used [KB]: 6140
% 1.11/0.52  % (24625)Time elapsed: 0.105 s
% 1.11/0.52  % (24625)------------------------------
% 1.11/0.52  % (24625)------------------------------
% 1.11/0.52  % (24620)Success in time 0.154 s
%------------------------------------------------------------------------------
