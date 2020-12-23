%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  19 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f9])).

fof(f9,plain,(
    k1_xboole_0 != k1_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f19,plain,(
    k1_xboole_0 = k1_setfam_1(sK0) ),
    inference(subsumption_resolution,[],[f18,f14])).

fof(f14,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f18,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_setfam_1(sK0))
    | k1_xboole_0 = k1_setfam_1(sK0) ),
    inference(resolution,[],[f17,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f17,plain,(
    r1_tarski(k1_setfam_1(sK0),k1_xboole_0) ),
    inference(resolution,[],[f8,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f8,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3723)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (3717)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (3717)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f19,f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    k1_xboole_0 != k1_setfam_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k1_xboole_0 = k1_setfam_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f18,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k1_setfam_1(sK0)) | k1_xboole_0 = k1_setfam_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f17,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    r1_tarski(k1_setfam_1(sK0),k1_xboole_0)),
% 0.21/0.49    inference(resolution,[],[f8,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3717)------------------------------
% 0.21/0.49  % (3717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3717)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3717)Memory used [KB]: 6012
% 0.21/0.49  % (3717)Time elapsed: 0.088 s
% 0.21/0.49  % (3717)------------------------------
% 0.21/0.49  % (3717)------------------------------
% 0.21/0.49  % (3735)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (3711)Success in time 0.137 s
%------------------------------------------------------------------------------
