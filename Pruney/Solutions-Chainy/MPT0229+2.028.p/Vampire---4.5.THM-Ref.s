%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  31 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  62 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f33])).

fof(f33,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f12,f12,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
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

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f36,plain,(
    r2_hidden(sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f21,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f21,plain,(
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f11,f14,f14])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f11,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:57:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (2294)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (2294)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f36,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ~r2_hidden(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f12,f12,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,k2_tarski(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    sK0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f25,f21,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f11,f14,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 0.22/0.51    inference(equality_resolution,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (2294)------------------------------
% 0.22/0.51  % (2294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2294)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (2294)Memory used [KB]: 10618
% 0.22/0.51  % (2294)Time elapsed: 0.090 s
% 0.22/0.51  % (2294)------------------------------
% 0.22/0.51  % (2294)------------------------------
% 0.22/0.51  % (2284)Success in time 0.14 s
%------------------------------------------------------------------------------
