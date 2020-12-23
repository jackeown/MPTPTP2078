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
% DateTime   : Thu Dec  3 12:38:33 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  62 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(resolution,[],[f29,f16])).

fof(f16,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
     => r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f28,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f27,f25])).

fof(f25,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f15,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f15,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n001.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.15/0.30  % WCLimit    : 600
% 0.15/0.30  % DateTime   : Tue Dec  1 15:10:15 EST 2020
% 0.15/0.30  % CPUTime    : 
% 0.16/0.37  % (24237)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.16/0.38  % (24229)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.16/0.39  % (24241)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.16/0.39  % (24229)Refutation found. Thanks to Tanya!
% 0.16/0.39  % SZS status Theorem for theBenchmark
% 0.16/0.39  % SZS output start Proof for theBenchmark
% 0.16/0.39  fof(f30,plain,(
% 0.16/0.39    $false),
% 0.16/0.39    inference(resolution,[],[f29,f16])).
% 0.16/0.39  fof(f16,plain,(
% 0.16/0.39    ~r2_hidden(sK0,sK1)),
% 0.16/0.39    inference(cnf_transformation,[],[f14])).
% 0.16/0.39  fof(f14,plain,(
% 0.16/0.39    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.16/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 0.16/0.39  fof(f13,plain,(
% 0.16/0.39    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.16/0.39    introduced(choice_axiom,[])).
% 0.16/0.39  fof(f10,plain,(
% 0.16/0.39    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.16/0.39    inference(ennf_transformation,[],[f8])).
% 0.16/0.39  fof(f8,negated_conjecture,(
% 0.16/0.39    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.16/0.39    inference(negated_conjecture,[],[f7])).
% 0.16/0.39  fof(f7,conjecture,(
% 0.16/0.39    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.16/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.16/0.39  fof(f29,plain,(
% 0.16/0.39    r2_hidden(sK0,sK1)),
% 0.16/0.39    inference(resolution,[],[f28,f20])).
% 0.16/0.39  fof(f20,plain,(
% 0.16/0.39    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.16/0.39    inference(cnf_transformation,[],[f11])).
% 0.16/0.39  fof(f11,plain,(
% 0.16/0.39    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))),
% 0.16/0.39    inference(ennf_transformation,[],[f9])).
% 0.16/0.39  fof(f9,plain,(
% 0.16/0.39    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) => r2_hidden(X0,X1))),
% 0.16/0.39    inference(unused_predicate_definition_removal,[],[f5])).
% 0.16/0.39  fof(f5,axiom,(
% 0.16/0.39    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.16/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.16/0.39  fof(f28,plain,(
% 0.16/0.39    r1_tarski(k1_tarski(sK0),sK1)),
% 0.16/0.39    inference(resolution,[],[f27,f25])).
% 0.16/0.39  fof(f25,plain,(
% 0.16/0.39    r1_tarski(k3_tarski(k6_enumset1(k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),k1_tarski(sK0),sK1)),sK1)),
% 0.16/0.39    inference(definition_unfolding,[],[f15,f24])).
% 0.16/0.39  fof(f24,plain,(
% 0.16/0.39    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.16/0.39    inference(definition_unfolding,[],[f17,f23])).
% 0.16/0.39  fof(f23,plain,(
% 0.16/0.39    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.16/0.39    inference(definition_unfolding,[],[f18,f21])).
% 0.16/0.39  fof(f21,plain,(
% 0.16/0.39    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.16/0.39    inference(cnf_transformation,[],[f4])).
% 0.16/0.39  fof(f4,axiom,(
% 0.16/0.39    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.16/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).
% 0.16/0.39  fof(f18,plain,(
% 0.16/0.39    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.16/0.39    inference(cnf_transformation,[],[f3])).
% 0.16/0.39  fof(f3,axiom,(
% 0.16/0.39    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.16/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.16/0.39  fof(f17,plain,(
% 0.16/0.39    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.16/0.39    inference(cnf_transformation,[],[f6])).
% 0.16/0.39  fof(f6,axiom,(
% 0.16/0.39    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.16/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.16/0.39  fof(f15,plain,(
% 0.16/0.39    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.16/0.39    inference(cnf_transformation,[],[f14])).
% 0.16/0.39  fof(f27,plain,(
% 0.16/0.39    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.16/0.39    inference(definition_unfolding,[],[f22,f24])).
% 0.16/0.39  fof(f22,plain,(
% 0.16/0.39    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.16/0.39    inference(cnf_transformation,[],[f12])).
% 0.16/0.39  fof(f12,plain,(
% 0.16/0.39    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.16/0.39    inference(ennf_transformation,[],[f1])).
% 0.16/0.39  fof(f1,axiom,(
% 0.16/0.39    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.16/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.16/0.39  % SZS output end Proof for theBenchmark
% 0.16/0.39  % (24229)------------------------------
% 0.16/0.39  % (24229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.39  % (24229)Termination reason: Refutation
% 0.16/0.39  
% 0.16/0.39  % (24229)Memory used [KB]: 6012
% 0.16/0.39  % (24229)Time elapsed: 0.046 s
% 0.16/0.39  % (24229)------------------------------
% 0.16/0.39  % (24229)------------------------------
% 0.16/0.39  % (24232)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.16/0.39  % (24226)Success in time 0.08 s
%------------------------------------------------------------------------------
