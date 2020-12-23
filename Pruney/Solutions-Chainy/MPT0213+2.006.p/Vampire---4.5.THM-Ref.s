%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  40 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 (  97 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f11])).

fof(f11,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f7])).

fof(f7,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f65,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK0(k1_xboole_0,X0),X0)
      | k3_tarski(k1_xboole_0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k3_tarski(k1_xboole_0) = X0
      | r2_hidden(sK0(k1_xboole_0,X0),X0)
      | r2_hidden(sK0(k1_xboole_0,X0),X0)
      | k3_tarski(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f52,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),k1_xboole_0)
      | k3_tarski(X0) = X1
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(superposition,[],[f37,f13])).

fof(f13,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f37,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK2(X9,X10),k4_xboole_0(X11,X9))
      | k3_tarski(X9) = X10
      | r2_hidden(sK0(X9,X10),X10) ) ),
    inference(resolution,[],[f17,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
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

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0)
      | k3_tarski(k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f58,f13])).

fof(f58,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK0(k1_xboole_0,X6),k4_xboole_0(X7,X6))
      | k3_tarski(k1_xboole_0) = X6 ) ),
    inference(resolution,[],[f54,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:23:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (6589)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (6581)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (6589)Refutation not found, incomplete strategy% (6589)------------------------------
% 0.22/0.51  % (6589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6573)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (6589)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6589)Memory used [KB]: 10618
% 0.22/0.51  % (6589)Time elapsed: 0.060 s
% 0.22/0.51  % (6589)------------------------------
% 0.22/0.51  % (6589)------------------------------
% 0.22/0.51  % (6573)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f65,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0) | k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f62,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK0(k1_xboole_0,X0),X0) | k3_tarski(k1_xboole_0) = X0) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0] : (k3_tarski(k1_xboole_0) = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0) | r2_hidden(sK0(k1_xboole_0,X0),X0) | k3_tarski(k1_xboole_0) = X0) )),
% 0.22/0.51    inference(resolution,[],[f52,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),k1_xboole_0) | k3_tarski(X0) = X1 | r2_hidden(sK0(X0,X1),X1)) )),
% 0.22/0.51    inference(superposition,[],[f37,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~r2_hidden(sK2(X9,X10),k4_xboole_0(X11,X9)) | k3_tarski(X9) = X10 | r2_hidden(sK0(X9,X10),X10)) )),
% 0.22/0.51    inference(resolution,[],[f17,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) | k3_tarski(k1_xboole_0) = X0) )),
% 0.22/0.51    inference(superposition,[],[f58,f13])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~r2_hidden(sK0(k1_xboole_0,X6),k4_xboole_0(X7,X6)) | k3_tarski(k1_xboole_0) = X6) )),
% 0.22/0.51    inference(resolution,[],[f54,f31])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (6573)------------------------------
% 0.22/0.51  % (6573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6573)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (6573)Memory used [KB]: 6268
% 0.22/0.51  % (6573)Time elapsed: 0.067 s
% 0.22/0.51  % (6573)------------------------------
% 0.22/0.51  % (6573)------------------------------
% 0.22/0.52  % (6566)Success in time 0.149 s
%------------------------------------------------------------------------------
