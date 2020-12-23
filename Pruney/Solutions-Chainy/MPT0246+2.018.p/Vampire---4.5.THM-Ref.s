%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  57 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 131 expanded)
%              Number of equality atoms :   28 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(resolution,[],[f111,f32])).

fof(f32,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f111,plain,(
    ~ r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
    inference(backward_demodulation,[],[f68,f108])).

fof(f108,plain,(
    sK1 = sK3(sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f67,f9])).

fof(f9,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

% (23939)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f67,plain,(
    r2_hidden(sK3(sK0,k2_tarski(sK1,sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f48,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    ~ r1_tarski(sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f11,f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f21,f24,f24])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f25,plain,(
    sK0 != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f10,f24])).

fof(f10,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    ~ r2_hidden(sK3(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (23922)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (23943)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (23938)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (23927)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (23930)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (23922)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (23938)Refutation not found, incomplete strategy% (23938)------------------------------
% 0.22/0.54  % (23938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f111,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 0.22/0.54    inference(equality_resolution,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k2_tarski(sK1,sK1))),
% 0.22/0.54    inference(backward_demodulation,[],[f68,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    sK1 = sK3(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f67,f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.54    inference(negated_conjecture,[],[f5])).
% 0.22/0.54  fof(f5,conjecture,(
% 0.22/0.54    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.22/0.54  % (23939)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f48,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ~r1_tarski(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f11,f25,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f21,f24,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    sK0 != k2_tarski(sK1,sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f10,f24])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    sK0 != k1_tarski(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f48,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (23922)------------------------------
% 0.22/0.54  % (23922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23922)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (23922)Memory used [KB]: 6268
% 0.22/0.54  % (23922)Time elapsed: 0.109 s
% 0.22/0.54  % (23922)------------------------------
% 0.22/0.54  % (23922)------------------------------
% 0.22/0.55  % (23917)Success in time 0.172 s
%------------------------------------------------------------------------------
