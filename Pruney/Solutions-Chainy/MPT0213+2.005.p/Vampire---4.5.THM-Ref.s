%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  23 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  40 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(subsumption_resolution,[],[f92,f9])).

fof(f9,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f5])).

fof(f5,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f92,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f39,f10])).

fof(f10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | k3_tarski(k1_xboole_0) = X3 ) ),
    inference(resolution,[],[f36,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK0(k1_xboole_0,X0),X0)
      | k3_tarski(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f22,f10])).

fof(f22,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X3)
      | k3_tarski(X3) = X4
      | r2_hidden(sK0(X3,X4),X4) ) ),
    inference(resolution,[],[f14,f11])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:45:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (9229)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (9229)Refutation not found, incomplete strategy% (9229)------------------------------
% 0.22/0.47  % (9229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (9229)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (9229)Memory used [KB]: 1535
% 0.22/0.47  % (9229)Time elapsed: 0.049 s
% 0.22/0.47  % (9229)------------------------------
% 0.22/0.47  % (9229)------------------------------
% 0.22/0.48  % (9233)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (9233)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f92,f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.48    inference(flattening,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.48    inference(resolution,[],[f39,f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X3] : (~v1_xboole_0(X3) | k3_tarski(k1_xboole_0) = X3) )),
% 0.22/0.48    inference(resolution,[],[f36,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK0(k1_xboole_0,X0),X0) | k3_tarski(k1_xboole_0) = X0) )),
% 0.22/0.48    inference(resolution,[],[f22,f10])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X4,X3] : (~v1_xboole_0(X3) | k3_tarski(X3) = X4 | r2_hidden(sK0(X3,X4),X4)) )),
% 0.22/0.48    inference(resolution,[],[f14,f11])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (9233)------------------------------
% 0.22/0.48  % (9233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (9233)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (9233)Memory used [KB]: 1791
% 0.22/0.48  % (9233)Time elapsed: 0.066 s
% 0.22/0.48  % (9233)------------------------------
% 0.22/0.48  % (9233)------------------------------
% 0.22/0.48  % (9214)Success in time 0.121 s
%------------------------------------------------------------------------------
