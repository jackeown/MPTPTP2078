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
% DateTime   : Thu Dec  3 12:46:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 105 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(subsumption_resolution,[],[f39,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f39,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f36,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f34,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f22,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f29,f20])).

fof(f29,plain,(
    ! [X0] : v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f25,f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f28,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f27,f21])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK3(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (31523)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (31523)Refutation not found, incomplete strategy% (31523)------------------------------
% 0.22/0.48  % (31523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31539)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (31523)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (31523)Memory used [KB]: 10490
% 0.22/0.48  % (31523)Time elapsed: 0.051 s
% 0.22/0.48  % (31523)------------------------------
% 0.22/0.48  % (31523)------------------------------
% 0.22/0.49  % (31539)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f39,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    k1_xboole_0 != sK0),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    k1_xboole_0 = sK0),
% 0.22/0.49    inference(resolution,[],[f36,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v1_xboole_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f28,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f34,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.49    inference(superposition,[],[f22,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(resolution,[],[f29,f20])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.49    inference(resolution,[],[f25,f19])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(resolution,[],[f22,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | v1_xboole_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f27,f21])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK3(k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.49    inference(resolution,[],[f24,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    r1_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK3(X1),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (31539)------------------------------
% 0.22/0.49  % (31539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (31539)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (31539)Memory used [KB]: 1663
% 0.22/0.49  % (31539)Time elapsed: 0.062 s
% 0.22/0.49  % (31539)------------------------------
% 0.22/0.49  % (31539)------------------------------
% 0.22/0.49  % (31528)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (31521)Success in time 0.122 s
%------------------------------------------------------------------------------
