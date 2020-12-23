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
% DateTime   : Thu Dec  3 12:32:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  50 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   13
%              Number of atoms          :   67 ( 117 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(resolution,[],[f76,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f76,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(superposition,[],[f53,f26])).

fof(f26,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f20,f16])).

fof(f16,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f53,plain,(
    ! [X4] : ~ r1_xboole_0(k2_xboole_0(sK0,X4),sK2) ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f37,plain,(
    ! [X1] : ~ r1_xboole_0(sK2,k2_xboole_0(sK0,X1)) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f35,plain,(
    ~ r1_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f31,f21])).

fof(f31,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f30,f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f28,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f28,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f25,f26])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (3608)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (3609)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (3611)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (3607)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (3607)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(resolution,[],[f76,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 0.21/0.43    inference(superposition,[],[f53,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(resolution,[],[f20,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X4] : (~r1_xboole_0(k2_xboole_0(sK0,X4),sK2)) )),
% 0.21/0.43    inference(resolution,[],[f37,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X1] : (~r1_xboole_0(sK2,k2_xboole_0(sK0,X1))) )),
% 0.21/0.43    inference(resolution,[],[f35,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~r1_xboole_0(sK2,sK0)),
% 0.21/0.43    inference(resolution,[],[f31,f21])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.43    inference(resolution,[],[f30,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(resolution,[],[f28,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),X0) | r1_tarski(sK0,X0)) )),
% 0.21/0.43    inference(superposition,[],[f25,f26])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (3607)------------------------------
% 0.21/0.43  % (3607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (3607)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (3607)Memory used [KB]: 6140
% 0.21/0.43  % (3607)Time elapsed: 0.005 s
% 0.21/0.43  % (3607)------------------------------
% 0.21/0.43  % (3607)------------------------------
% 0.21/0.43  % (3602)Success in time 0.067 s
%------------------------------------------------------------------------------
