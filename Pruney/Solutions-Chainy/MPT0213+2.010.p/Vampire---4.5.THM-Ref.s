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
% DateTime   : Thu Dec  3 12:34:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  93 expanded)
%              Number of leaves         :    5 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 ( 189 expanded)
%              Number of equality atoms :   18 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(subsumption_resolution,[],[f77,f74])).

fof(f74,plain,(
    ! [X8] : r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X8) ),
    inference(subsumption_resolution,[],[f71,f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f71,plain,(
    ! [X8] :
      ( k1_xboole_0 = k3_tarski(k1_xboole_0)
      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X8) ) ),
    inference(resolution,[],[f66,f35])).

fof(f35,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X1) ) ),
    inference(superposition,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f11,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f66,plain,(
    ! [X6] :
      ( r2_hidden(sK0(k1_xboole_0,X6),X6)
      | k3_tarski(k1_xboole_0) = X6 ) ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK0(k1_xboole_0,X12),X12)
      | r2_hidden(sK2(k1_xboole_0,X12),X13)
      | k3_tarski(k1_xboole_0) = X12 ) ),
    inference(resolution,[],[f15,f35])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f61,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK0(k1_xboole_0,X6),X6)
      | k3_tarski(k1_xboole_0) = X6
      | ~ r2_hidden(sK2(k1_xboole_0,X6),k4_xboole_0(X8,X7)) ) ),
    inference(resolution,[],[f42,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X4,X5] : ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X4,X5)) ),
    inference(resolution,[],[f74,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (27329)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (27345)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (27337)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (27325)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (27326)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (27345)Refutation not found, incomplete strategy% (27345)------------------------------
% 0.21/0.51  % (27345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27345)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27345)Memory used [KB]: 10618
% 0.21/0.51  % (27345)Time elapsed: 0.106 s
% 0.21/0.51  % (27345)------------------------------
% 0.21/0.51  % (27345)------------------------------
% 0.21/0.51  % (27339)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (27324)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (27329)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f77,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X8] : (r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X8)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f71,f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X8] : (k1_xboole_0 = k3_tarski(k1_xboole_0) | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X8)) )),
% 0.21/0.52    inference(resolution,[],[f66,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X3,X1] : (~r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,X1)) )),
% 0.21/0.52    inference(superposition,[],[f31,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f11,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X6] : (r2_hidden(sK0(k1_xboole_0,X6),X6) | k3_tarski(k1_xboole_0) = X6) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f61,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X12,X13] : (r2_hidden(sK0(k1_xboole_0,X12),X12) | r2_hidden(sK2(k1_xboole_0,X12),X13) | k3_tarski(k1_xboole_0) = X12) )),
% 0.21/0.52    inference(resolution,[],[f15,f35])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X6,X8,X7] : (r2_hidden(sK0(k1_xboole_0,X6),X6) | k3_tarski(k1_xboole_0) = X6 | ~r2_hidden(sK2(k1_xboole_0,X6),k4_xboole_0(X8,X7))) )),
% 0.21/0.52    inference(resolution,[],[f42,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X4,X5))) )),
% 0.21/0.52    inference(resolution,[],[f74,f30])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (27329)------------------------------
% 0.21/0.52  % (27329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27329)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (27329)Memory used [KB]: 6268
% 0.21/0.52  % (27329)Time elapsed: 0.110 s
% 0.21/0.52  % (27329)------------------------------
% 0.21/0.52  % (27329)------------------------------
% 0.21/0.52  % (27322)Success in time 0.161 s
%------------------------------------------------------------------------------
