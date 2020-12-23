%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  95 expanded)
%              Number of leaves         :    4 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 259 expanded)
%              Number of equality atoms :   20 (  80 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(global_subsumption,[],[f72,f77])).

fof(f77,plain,(
    ~ r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f65,f25])).

fof(f25,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f65,plain,(
    ~ r2_hidden(sK5(k1_setfam_1(k1_xboole_0),sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f37,f53])).

fof(f53,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f34,f30,f28])).

fof(f28,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_setfam_1(X0))
      | sP3(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    r2_hidden(sK5(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f10,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f10,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f34,plain,(
    ~ sP3(sK5(k1_setfam_1(sK1),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f9,f31,f14])).

fof(f14,plain,(
    ! [X2,X0,X3] :
      ( ~ sP3(X2,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ~ r2_hidden(sK5(k1_setfam_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f10,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ~ r2_hidden(sK5(k1_setfam_1(sK1),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f11,f31,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f72,plain,(
    r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f60,f25])).

fof(f60,plain,(
    r2_hidden(sK5(k1_setfam_1(k1_xboole_0),sK0),k1_setfam_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f30,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.55  % (27249)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (27246)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (27270)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (27246)Refutation not found, incomplete strategy% (27246)------------------------------
% 0.21/0.56  % (27246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27246)Memory used [KB]: 1663
% 0.21/0.56  % (27246)Time elapsed: 0.123 s
% 0.21/0.56  % (27246)------------------------------
% 0.21/0.56  % (27246)------------------------------
% 0.21/0.57  % (27270)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(global_subsumption,[],[f72,f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ~r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f65,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 0.21/0.57    inference(equality_resolution,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = X1 | k1_setfam_1(k1_xboole_0) != X1) )),
% 0.21/0.57    inference(equality_resolution,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = X1 | k1_setfam_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ~r2_hidden(sK5(k1_setfam_1(k1_xboole_0),sK0),k1_xboole_0)),
% 0.21/0.57    inference(backward_demodulation,[],[f37,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    k1_xboole_0 = sK1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f34,f30,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_setfam_1(X0)) | sP3(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(equality_resolution,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | sP3(X2,X0) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    r2_hidden(sK5(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1))),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f10,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ~r1_tarski(k1_setfam_1(sK1),sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.57    inference(negated_conjecture,[],[f4])).
% 0.21/0.57  fof(f4,conjecture,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ~sP3(sK5(k1_setfam_1(sK1),sK0),sK1)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f9,f31,f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ( ! [X2,X0,X3] : (~sP3(X2,X0) | r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ~r2_hidden(sK5(k1_setfam_1(sK1),sK0),sK0)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f10,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    r2_hidden(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ~r2_hidden(sK5(k1_setfam_1(sK1),sK0),k1_xboole_0)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f11,f31,f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f60,f25])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    r2_hidden(sK5(k1_setfam_1(k1_xboole_0),sK0),k1_setfam_1(k1_xboole_0))),
% 0.21/0.57    inference(backward_demodulation,[],[f30,f53])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (27270)------------------------------
% 0.21/0.57  % (27270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27270)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (27270)Memory used [KB]: 6268
% 0.21/0.57  % (27270)Time elapsed: 0.141 s
% 0.21/0.57  % (27270)------------------------------
% 0.21/0.57  % (27270)------------------------------
% 0.21/0.57  % (27245)Success in time 0.21 s
%------------------------------------------------------------------------------
