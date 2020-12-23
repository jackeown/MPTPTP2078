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
% DateTime   : Thu Dec  3 12:36:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  44 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  77 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(resolution,[],[f101,f53])).

fof(f53,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f101,plain,(
    ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[],[f80,f75])).

fof(f75,plain,(
    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f37,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f13,f36,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f80,plain,(
    ! [X0] : ~ r2_hidden(sK0,k3_xboole_0(X0,k1_enumset1(sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f74,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f74,plain,(
    ~ r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f14,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f17,f36])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (10577)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.47  % (10585)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.48  % (10585)Refutation not found, incomplete strategy% (10585)------------------------------
% 0.20/0.48  % (10585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (10585)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (10585)Memory used [KB]: 10618
% 0.20/0.48  % (10585)Time elapsed: 0.078 s
% 0.20/0.48  % (10585)------------------------------
% 0.20/0.48  % (10585)------------------------------
% 0.20/0.51  % (10595)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (10595)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(resolution,[],[f101,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X4,X2,X1] : (r2_hidden(X4,k1_enumset1(X4,X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X4,X1,X2) != X3) )),
% 0.20/0.51    inference(equality_resolution,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 0.20/0.51    inference(superposition,[],[f80,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f37,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.51    inference(definition_unfolding,[],[f13,f36,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f20,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,k3_xboole_0(X0,k1_enumset1(sK1,sK1,sK1)))) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f74,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f14,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 0.20/0.52    inference(equality_resolution,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f17,f36])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    sK0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (10595)------------------------------
% 0.20/0.52  % (10595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10595)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (10595)Memory used [KB]: 6268
% 0.20/0.52  % (10595)Time elapsed: 0.098 s
% 0.20/0.52  % (10595)------------------------------
% 0.20/0.52  % (10595)------------------------------
% 0.20/0.52  % (10568)Success in time 0.161 s
%------------------------------------------------------------------------------
