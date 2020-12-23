%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   14 (  17 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f16,f17,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f17,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f7,f8])).

fof(f8,plain,(
    sK0 = sK1 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( X0 = X1
      & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( X0 = X1
          & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f7,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f9])).

fof(f9,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:10:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (30027)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (30034)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (30036)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (30034)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f16,f17,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.50    inference(forward_demodulation,[],[f7,f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    sK0 = sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,plain,(
% 0.22/0.50    ? [X0,X1] : (X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f3])).
% 0.22/0.50  fof(f3,conjecture,(
% 0.22/0.50    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.22/0.50    inference(equality_resolution,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.22/0.50    inference(equality_resolution,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (30034)------------------------------
% 0.22/0.50  % (30034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30034)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (30034)Memory used [KB]: 1535
% 0.22/0.50  % (30034)Time elapsed: 0.066 s
% 0.22/0.50  % (30034)------------------------------
% 0.22/0.50  % (30034)------------------------------
% 0.22/0.50  % (30026)Success in time 0.137 s
%------------------------------------------------------------------------------
