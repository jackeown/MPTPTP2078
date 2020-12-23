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
% DateTime   : Thu Dec  3 12:29:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 160 expanded)
%              Number of leaves         :    3 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :   74 ( 381 expanded)
%              Number of equality atoms :   24 ( 120 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(subsumption_resolution,[],[f391,f8])).

fof(f8,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X0))
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f391,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f390,f21])).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f7,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f7,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f390,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f384,f340])).

fof(f340,plain,(
    ! [X22] :
      ( r2_hidden(sK2(sK0,X22,sK0),k1_xboole_0)
      | sK0 = k4_xboole_0(sK0,X22) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X22] :
      ( r2_hidden(sK2(sK0,X22,sK0),k1_xboole_0)
      | sK0 = k4_xboole_0(sK0,X22)
      | r2_hidden(sK2(sK0,X22,sK0),k1_xboole_0) ) ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f37,f19])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
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

fof(f37,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,k4_xboole_0(sK1,sK0)) ) ),
    inference(superposition,[],[f18,f21])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,X5,sK0),k1_xboole_0)
      | r2_hidden(sK2(X4,X5,sK0),X4)
      | sK0 = k4_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f40,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f384,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK1,sK0),sK0),k1_xboole_0) ),
    inference(resolution,[],[f371,f38])).

fof(f38,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k4_xboole_0(sK1,sK0))
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(superposition,[],[f19,f21])).

fof(f371,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0,sK0),X0)
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f370,f346])).

fof(f346,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0,sK0),sK0)
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f340,f39])).

fof(f39,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f20,f21])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f370,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK0,X0)
      | r2_hidden(sK2(sK0,X0,sK0),X0)
      | ~ r2_hidden(sK2(sK0,X0,sK0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK0,X0)
      | r2_hidden(sK2(sK0,X0,sK0),X0)
      | ~ r2_hidden(sK2(sK0,X0,sK0),sK0)
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f346,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (31156)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (31160)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (31157)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (31149)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (31156)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f392,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f391,f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_xboole_0 != X0 & r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.48  fof(f391,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(forward_demodulation,[],[f390,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.48    inference(resolution,[],[f7,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    r1_tarski(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f390,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f384,f340])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    ( ! [X22] : (r2_hidden(sK2(sK0,X22,sK0),k1_xboole_0) | sK0 = k4_xboole_0(sK0,X22)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f338])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    ( ! [X22] : (r2_hidden(sK2(sK0,X22,sK0),k1_xboole_0) | sK0 = k4_xboole_0(sK0,X22) | r2_hidden(sK2(sK0,X22,sK0),k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f49,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(X3,sK0) | r2_hidden(X3,k1_xboole_0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f37,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,sK0) | r2_hidden(X3,k4_xboole_0(sK1,sK0))) )),
% 0.21/0.48    inference(superposition,[],[f18,f21])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X4,X5] : (r2_hidden(sK2(X4,X5,sK0),k1_xboole_0) | r2_hidden(sK2(X4,X5,sK0),X4) | sK0 = k4_xboole_0(X4,X5)) )),
% 0.21/0.48    inference(resolution,[],[f40,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK1,sK0),sK0),k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f371,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(sK1,sK0)) | ~r2_hidden(X4,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f19,f21])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(sK0,X0,sK0),X0) | sK0 = k4_xboole_0(sK0,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f370,f346])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(sK0,X0,sK0),sK0) | sK0 = k4_xboole_0(sK0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f340,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,sK0)) )),
% 0.21/0.48    inference(superposition,[],[f20,f21])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ( ! [X0] : (sK0 = k4_xboole_0(sK0,X0) | r2_hidden(sK2(sK0,X0,sK0),X0) | ~r2_hidden(sK2(sK0,X0,sK0),sK0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f364])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    ( ! [X0] : (sK0 = k4_xboole_0(sK0,X0) | r2_hidden(sK2(sK0,X0,sK0),X0) | ~r2_hidden(sK2(sK0,X0,sK0),sK0) | sK0 = k4_xboole_0(sK0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f346,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31156)------------------------------
% 0.21/0.48  % (31156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31156)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31156)Memory used [KB]: 1791
% 0.21/0.48  % (31156)Time elapsed: 0.070 s
% 0.21/0.48  % (31156)------------------------------
% 0.21/0.48  % (31156)------------------------------
% 0.21/0.48  % (31150)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (31142)Success in time 0.127 s
%------------------------------------------------------------------------------
