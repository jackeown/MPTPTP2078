%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  46 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  83 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12876)Refutation not found, incomplete strategy% (12876)------------------------------
% (12876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f51,plain,(
    $false ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ~ r2_hidden(sK6(sK0,k2_setfam_1(sK0,sK0)),k2_setfam_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

% (12876)Termination reason: Refutation not found, incomplete strategy
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f30,plain,(
    ~ r1_tarski(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f11,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f11,plain,(
    ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

fof(f37,plain,(
    r2_hidden(sK6(sK0,k2_setfam_1(sK0,sK0)),k2_setfam_1(sK0,sK0)) ),
    inference(forward_demodulation,[],[f36,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f36,plain,(
    r2_hidden(k2_xboole_0(sK6(sK0,k2_setfam_1(sK0,sK0)),sK6(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f32,f32,f26])).

fof(f26,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k2_xboole_0(X4,X5),X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k2_xboole_0(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

fof(f32,plain,(
    r2_hidden(sK6(sK0,k2_setfam_1(sK0,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (12892)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (12876)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (12878)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (12878)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (12876)Refutation not found, incomplete strategy% (12876)------------------------------
% 0.21/0.50  % (12876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(resolution,[],[f37,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ~r2_hidden(sK6(sK0,k2_setfam_1(sK0,sK0)),k2_setfam_1(sK0,sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f30,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  % (12876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~r1_tarski(sK0,k2_setfam_1(sK0,sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f11,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ~r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    r2_hidden(sK6(sK0,k2_setfam_1(sK0,sK0)),k2_setfam_1(sK0,sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f36,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.50    inference(rectify,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    r2_hidden(k2_xboole_0(sK6(sK0,k2_setfam_1(sK0,sK0)),sK6(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f32,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k2_xboole_0(X4,X5),X2) | k2_setfam_1(X0,X1) != X2) )),
% 0.21/0.50    inference(equality_resolution,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k2_xboole_0(X4,X5) != X3 | r2_hidden(X3,X2) | k2_setfam_1(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    r2_hidden(sK6(sK0,k2_setfam_1(sK0,sK0)),sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f30,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (12878)------------------------------
% 0.21/0.50  % (12878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12878)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (12878)Memory used [KB]: 6140
% 0.21/0.50  % (12878)Time elapsed: 0.097 s
% 0.21/0.50  % (12878)------------------------------
% 0.21/0.50  % (12878)------------------------------
% 0.21/0.50  
% 0.21/0.50  % (12876)Memory used [KB]: 10618
% 0.21/0.50  % (12876)Time elapsed: 0.096 s
% 0.21/0.50  % (12876)------------------------------
% 0.21/0.50  % (12876)------------------------------
% 0.21/0.50  % (12871)Success in time 0.14 s
%------------------------------------------------------------------------------
