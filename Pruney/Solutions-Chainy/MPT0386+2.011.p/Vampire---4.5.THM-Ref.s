%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  45 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 110 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f28,f69,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f69,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f59,f30])).

fof(f30,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f59,plain,(
    k1_xboole_0 != k4_xboole_0(k1_setfam_1(k1_xboole_0),sK0) ),
    inference(backward_demodulation,[],[f39,f51])).

fof(f51,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f12,f41,f40,f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    r2_hidden(sK2(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f13,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f13,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f41,plain,(
    ~ r2_hidden(sK2(k1_setfam_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f13,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    k1_xboole_0 != k4_xboole_0(k1_setfam_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f13,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (14155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (14147)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (14149)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (14141)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (14139)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (14155)Refutation not found, incomplete strategy% (14155)------------------------------
% 0.22/0.52  % (14155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14155)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14155)Memory used [KB]: 10618
% 0.22/0.52  % (14155)Time elapsed: 0.103 s
% 0.22/0.52  % (14155)------------------------------
% 0.22/0.52  % (14155)------------------------------
% 0.22/0.52  % (14144)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (14139)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f28,f69,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f59,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 0.22/0.52    inference(equality_resolution,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = X1 | k1_setfam_1(k1_xboole_0) != X1) )),
% 0.22/0.52    inference(equality_resolution,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = X1 | k1_setfam_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(k1_setfam_1(k1_xboole_0),sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f39,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f12,f41,f40,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k1_xboole_0 = X0 | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    r2_hidden(sK2(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1))),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f13,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(sK1),sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f6])).
% 0.22/0.52  fof(f6,conjecture,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ~r2_hidden(sK2(k1_setfam_1(sK1),sK0),sK0)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f13,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(k1_setfam_1(sK1),sK0)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f13,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (14139)------------------------------
% 0.22/0.52  % (14139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14139)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (14139)Memory used [KB]: 6268
% 0.22/0.52  % (14139)Time elapsed: 0.109 s
% 0.22/0.52  % (14139)------------------------------
% 0.22/0.52  % (14139)------------------------------
% 0.22/0.52  % (14138)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (14134)Success in time 0.156 s
%------------------------------------------------------------------------------
