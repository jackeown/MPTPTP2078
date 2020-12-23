%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:53 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   20 (  28 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  59 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f46,f54,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f12])).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f54,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f23,plain,(
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f9,f12])).

fof(f9,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f46,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f10,f11,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
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

fof(f11,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.30/0.55  % (29046)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.55  % (29023)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.56  % (29032)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.52/0.56  % (29046)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.57  % (29033)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.52/0.57  % (29038)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f46,f54,f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f22,f12])).
% 1.52/0.57  fof(f12,plain,(
% 1.52/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f23,f13])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.52/0.57    inference(definition_unfolding,[],[f9,f12])).
% 1.52/0.57  fof(f9,plain,(
% 1.52/0.57    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,plain,(
% 1.52/0.57    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.52/0.57    inference(negated_conjecture,[],[f6])).
% 1.52/0.57  fof(f6,conjecture,(
% 1.52/0.57    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ~r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f10,f11,f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.52/0.57    inference(equality_resolution,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.52/0.57    inference(cnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.52/0.57  fof(f11,plain,(
% 1.52/0.57    sK0 != sK2),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f10,plain,(
% 1.52/0.57    sK0 != sK1),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (29046)------------------------------
% 1.52/0.57  % (29046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (29046)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (29046)Memory used [KB]: 6140
% 1.52/0.57  % (29046)Time elapsed: 0.137 s
% 1.52/0.57  % (29046)------------------------------
% 1.52/0.57  % (29046)------------------------------
% 1.52/0.57  % (29047)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.52/0.57  % (29022)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.52/0.57  % (29020)Success in time 0.203 s
%------------------------------------------------------------------------------
