%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  41 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  94 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f13,f32,f35,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f35,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f15,f32,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f32,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(subsumption_resolution,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k4_xboole_0(sK1,sK0)) ) ),
    inference(resolution,[],[f12,f16])).

fof(f12,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X0))
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (22471)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (22471)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (22470)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f13,f32,f35,f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f15,f32,f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f28,f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(equality_resolution,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k4_xboole_0(sK1,sK0))) )),
% 0.22/0.56    inference(resolution,[],[f12,f16])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    r1_tarski(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ? [X0,X1] : (k1_xboole_0 != X0 & r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.22/0.56    inference(negated_conjecture,[],[f6])).
% 0.22/0.56  fof(f6,conjecture,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    k1_xboole_0 != sK0),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (22471)------------------------------
% 0.22/0.56  % (22471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22471)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (22471)Memory used [KB]: 10746
% 0.22/0.56  % (22471)Time elapsed: 0.123 s
% 0.22/0.56  % (22471)------------------------------
% 0.22/0.56  % (22471)------------------------------
% 0.22/0.56  % (22470)Refutation not found, incomplete strategy% (22470)------------------------------
% 0.22/0.56  % (22470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22470)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22470)Memory used [KB]: 10618
% 0.22/0.56  % (22470)Time elapsed: 0.129 s
% 0.22/0.56  % (22470)------------------------------
% 0.22/0.56  % (22470)------------------------------
% 0.22/0.56  % (22463)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.56  % (22461)Success in time 0.197 s
%------------------------------------------------------------------------------
