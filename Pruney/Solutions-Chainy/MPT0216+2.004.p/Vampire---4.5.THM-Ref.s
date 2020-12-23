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
% DateTime   : Thu Dec  3 12:35:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  93 expanded)
%              Number of leaves         :    4 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 167 expanded)
%              Number of equality atoms :   39 ( 136 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f64,f47,f64,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f16,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f47,plain,(
    r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[],[f38,f28])).

fof(f28,plain,(
    k1_enumset1(sK0,sK0,sK0) = k1_enumset1(sK1,sK1,sK2) ),
    inference(definition_unfolding,[],[f9,f27,f12])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f11,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f9,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f38,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f17,f12])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f10,f60])).

fof(f60,plain,(
    sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[],[f36,f28])).

fof(f36,plain,(
    ! [X0,X3] : r2_hidden(X3,k1_enumset1(X0,X0,X3)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f18,f12])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:00:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (20929)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (20920)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (20927)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (20927)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f64,f47,f64,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.21/0.50    inference(equality_resolution,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.50    inference(definition_unfolding,[],[f16,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.50    inference(superposition,[],[f38,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK0,sK0) = k1_enumset1(sK1,sK1,sK2)),
% 0.21/0.50    inference(definition_unfolding,[],[f9,f27,f12])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f11,f12])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.50    inference(definition_unfolding,[],[f17,f12])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    sK0 != sK1),
% 0.21/0.50    inference(superposition,[],[f10,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    sK0 = sK2),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    sK0 = sK2 | sK0 = sK2),
% 0.21/0.50    inference(resolution,[],[f39,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.50    inference(superposition,[],[f36,f28])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X3] : (r2_hidden(X3,k1_enumset1(X0,X0,X3))) )),
% 0.21/0.50    inference(equality_resolution,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k1_enumset1(X0,X0,X3) != X2) )),
% 0.21/0.50    inference(equality_resolution,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.50    inference(definition_unfolding,[],[f18,f12])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    sK1 != sK2),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (20927)------------------------------
% 0.21/0.50  % (20927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20927)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (20927)Memory used [KB]: 6268
% 0.21/0.50  % (20927)Time elapsed: 0.089 s
% 0.21/0.50  % (20927)------------------------------
% 0.21/0.50  % (20927)------------------------------
% 0.21/0.51  % (20913)Success in time 0.14 s
%------------------------------------------------------------------------------
