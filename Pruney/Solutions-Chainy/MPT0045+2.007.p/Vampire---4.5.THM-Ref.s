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
% DateTime   : Thu Dec  3 12:29:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  55 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 134 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X0))
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f64,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK2(X5,k1_xboole_0),k4_xboole_0(X6,X5))
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0,k1_xboole_0),X0)
      | r2_hidden(sK2(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X1,X0),k1_xboole_0)
      | X0 = X1
      | r2_hidden(sK2(X1,X0),X1) ) ),
    inference(superposition,[],[f29,f13])).

fof(f13,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f29,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK2(X6,X7),k4_xboole_0(X8,X7))
      | X6 = X7
      | r2_hidden(sK2(X6,X7),X6) ) ),
    inference(resolution,[],[f14,f24])).

fof(f63,plain,(
    r2_hidden(sK2(sK0,k1_xboole_0),k4_xboole_0(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f62,f12])).

fof(f62,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0,k1_xboole_0),k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f50,f11])).

fof(f11,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k1_xboole_0 = X3
      | r2_hidden(sK2(X3,k1_xboole_0),X4) ) ),
    inference(resolution,[],[f45,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (27684)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (27675)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (27693)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (27685)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (27673)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (27676)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (27675)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (27692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f64,f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1] : (k1_xboole_0 != X0 & r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.52    inference(negated_conjecture,[],[f5])).
% 0.20/0.52  fof(f5,conjecture,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    k1_xboole_0 = sK0),
% 0.20/0.52    inference(resolution,[],[f63,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~r2_hidden(sK2(X5,k1_xboole_0),k4_xboole_0(X6,X5)) | k1_xboole_0 = X5) )),
% 0.20/0.52    inference(resolution,[],[f45,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK2(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0,k1_xboole_0),X0) | r2_hidden(sK2(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(resolution,[],[f40,f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X1,X0),k1_xboole_0) | X0 = X1 | r2_hidden(sK2(X1,X0),X1)) )),
% 0.20/0.52    inference(superposition,[],[f29,f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (~r2_hidden(sK2(X6,X7),k4_xboole_0(X8,X7)) | X6 = X7 | r2_hidden(sK2(X6,X7),X6)) )),
% 0.20/0.52    inference(resolution,[],[f14,f24])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    r2_hidden(sK2(sK0,k1_xboole_0),k4_xboole_0(sK1,sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f62,f12])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | r2_hidden(sK2(sK0,k1_xboole_0),k4_xboole_0(sK1,sK0))),
% 0.20/0.52    inference(resolution,[],[f50,f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    r1_tarski(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k1_xboole_0 = X3 | r2_hidden(sK2(X3,k1_xboole_0),X4)) )),
% 0.20/0.52    inference(resolution,[],[f45,f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (27675)------------------------------
% 0.20/0.52  % (27675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27675)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (27675)Memory used [KB]: 6140
% 0.20/0.52  % (27675)Time elapsed: 0.105 s
% 0.20/0.52  % (27675)------------------------------
% 0.20/0.52  % (27675)------------------------------
% 0.20/0.52  % (27667)Success in time 0.161 s
%------------------------------------------------------------------------------
