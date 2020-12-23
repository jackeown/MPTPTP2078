%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 151 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :   78 ( 381 expanded)
%              Number of equality atoms :   21 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f37,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f35,f29])).

fof(f29,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_tarski(X3,X5),X4)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f10,f22])).

fof(f22,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
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

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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

fof(f35,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f34,f7])).

fof(f7,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f34,plain,(
    r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f31])).

fof(f31,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f28,f9])).

fof(f9,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X2,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f10,f20])).

fof(f20,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f73,f39])).

fof(f39,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f37,f8])).

fof(f8,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f12,f70])).

fof(f70,plain,(
    sK0 = sK3(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f69,f37])).

fof(f69,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f66,f34])).

fof(f66,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2)
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f12,f62])).

fof(f62,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2)
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f50,f37])).

fof(f50,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k2_tarski(X5,X4),X6)
      | sK3(k2_tarski(X5,X4),X6) = X5
      | sK3(k2_tarski(X5,X4),X6) = X4 ) ),
    inference(resolution,[],[f23,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (15520)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.46  % (15497)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.46  % (15497)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f75,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f35,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~r1_tarski(k2_tarski(X3,X5),X4) | r2_hidden(X3,X4)) )),
% 0.21/0.46    inference(resolution,[],[f10,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 0.21/0.46    inference(equality_resolution,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 0.21/0.46    inference(equality_resolution,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(resolution,[],[f34,f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    r2_hidden(sK1,sK2) | r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(resolution,[],[f28,f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    r1_tarski(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X2,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(resolution,[],[f10,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X3] : (r2_hidden(X3,k2_tarski(X0,X3))) )),
% 0.21/0.46    inference(equality_resolution,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_tarski(X0,X3) != X2) )),
% 0.21/0.46    inference(equality_resolution,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f73,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    r2_hidden(sK0,sK2)),
% 0.21/0.46    inference(resolution,[],[f37,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    r1_tarski(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ~r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(superposition,[],[f12,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    sK0 = sK3(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f69,f37])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    r1_tarski(k2_tarski(sK0,sK1),sK2) | sK0 = sK3(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f66,f34])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ~r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2) | sK0 = sK3(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(superposition,[],[f12,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    sK1 = sK3(k2_tarski(sK0,sK1),sK2) | sK0 = sK3(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(resolution,[],[f50,f37])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X6,X4,X5] : (r1_tarski(k2_tarski(X5,X4),X6) | sK3(k2_tarski(X5,X4),X6) = X5 | sK3(k2_tarski(X5,X4),X6) = X4) )),
% 0.21/0.46    inference(resolution,[],[f23,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.21/0.46    inference(equality_resolution,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (15497)------------------------------
% 0.21/0.46  % (15497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (15497)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (15497)Memory used [KB]: 6268
% 0.21/0.46  % (15497)Time elapsed: 0.047 s
% 0.21/0.46  % (15497)------------------------------
% 0.21/0.46  % (15497)------------------------------
% 0.21/0.46  % (15490)Success in time 0.108 s
%------------------------------------------------------------------------------
