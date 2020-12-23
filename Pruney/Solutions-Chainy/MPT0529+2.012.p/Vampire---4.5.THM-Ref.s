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
% DateTime   : Thu Dec  3 12:48:59 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   41 (  97 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 245 expanded)
%              Number of equality atoms :   28 (  74 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f21,f253,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X1,k8_relat_1(X0,sK2)))
      | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) ) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    ! [X4,X3] : r1_tarski(k8_relat_1(X3,k8_relat_1(X4,sK2)),k8_relat_1(X4,sK2)) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f23,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f253,plain,(
    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,k8_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f126,f47])).

fof(f47,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2)) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    inference(resolution,[],[f29,f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f126,plain,(
    ! [X0] : r1_tarski(k8_relat_1(sK0,k8_relat_1(X0,sK2)),k8_relat_1(sK1,k8_relat_1(X0,sK2))) ),
    inference(superposition,[],[f49,f74])).

fof(f74,plain,(
    ! [X0] : k8_relat_1(sK0,k8_relat_1(sK1,k8_relat_1(X0,sK2))) = k8_relat_1(sK0,k8_relat_1(X0,sK2)) ),
    inference(superposition,[],[f39,f34])).

fof(f34,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,sK2))) = k8_relat_1(k3_xboole_0(X0,X1),k8_relat_1(X2,sK2)) ),
    inference(resolution,[],[f32,f29])).

fof(f49,plain,(
    ! [X6,X4,X5] : r1_tarski(k8_relat_1(X4,k8_relat_1(X5,k8_relat_1(X6,sK2))),k8_relat_1(X5,k8_relat_1(X6,sK2))) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X6,X5] : v1_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK2))) ),
    inference(resolution,[],[f32,f23])).

fof(f21,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:12:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.51  % (31006)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.18/0.53  % (31022)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.18/0.53  % (31014)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.18/0.54  % (31006)Refutation found. Thanks to Tanya!
% 0.18/0.54  % SZS status Theorem for theBenchmark
% 0.18/0.55  % SZS output start Proof for theBenchmark
% 0.18/0.55  fof(f335,plain,(
% 0.18/0.55    $false),
% 0.18/0.55    inference(unit_resulting_resolution,[],[f21,f253,f55])).
% 0.18/0.55  fof(f55,plain,(
% 0.18/0.55    ( ! [X0,X1] : (~r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X1,k8_relat_1(X0,sK2))) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) )),
% 0.18/0.55    inference(resolution,[],[f40,f28])).
% 0.18/0.55  fof(f28,plain,(
% 0.18/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f18])).
% 0.18/0.55  fof(f18,plain,(
% 0.18/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.55    inference(flattening,[],[f17])).
% 0.18/0.55  fof(f17,plain,(
% 0.18/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.55    inference(nnf_transformation,[],[f1])).
% 0.18/0.55  fof(f1,axiom,(
% 0.18/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.55  fof(f40,plain,(
% 0.18/0.55    ( ! [X4,X3] : (r1_tarski(k8_relat_1(X3,k8_relat_1(X4,sK2)),k8_relat_1(X4,sK2))) )),
% 0.18/0.55    inference(resolution,[],[f32,f24])).
% 0.18/0.55  fof(f24,plain,(
% 0.18/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f12])).
% 0.18/0.55  fof(f12,plain,(
% 0.18/0.55    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.18/0.55    inference(ennf_transformation,[],[f5])).
% 0.18/0.55  fof(f5,axiom,(
% 0.18/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.18/0.55  fof(f32,plain,(
% 0.18/0.55    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 0.18/0.55    inference(resolution,[],[f23,f19])).
% 0.18/0.55  fof(f19,plain,(
% 0.18/0.55    v1_relat_1(sK2)),
% 0.18/0.55    inference(cnf_transformation,[],[f16])).
% 0.18/0.55  fof(f16,plain,(
% 0.18/0.55    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.18/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.18/0.55  fof(f15,plain,(
% 0.18/0.55    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.18/0.55    introduced(choice_axiom,[])).
% 0.18/0.55  fof(f10,plain,(
% 0.18/0.55    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.18/0.55    inference(flattening,[],[f9])).
% 0.18/0.55  fof(f9,plain,(
% 0.18/0.55    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.18/0.55    inference(ennf_transformation,[],[f8])).
% 0.18/0.55  fof(f8,negated_conjecture,(
% 0.18/0.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.18/0.55    inference(negated_conjecture,[],[f7])).
% 0.18/0.55  fof(f7,conjecture,(
% 0.18/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.18/0.55  fof(f23,plain,(
% 0.18/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.18/0.55    inference(cnf_transformation,[],[f11])).
% 0.18/0.55  fof(f11,plain,(
% 0.18/0.55    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.18/0.55    inference(ennf_transformation,[],[f4])).
% 0.18/0.55  fof(f4,axiom,(
% 0.18/0.55    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.18/0.55  fof(f253,plain,(
% 0.18/0.55    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,k8_relat_1(sK0,sK2)))),
% 0.18/0.55    inference(superposition,[],[f126,f47])).
% 0.18/0.55  fof(f47,plain,(
% 0.18/0.55    ( ! [X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))) )),
% 0.18/0.55    inference(superposition,[],[f38,f35])).
% 0.18/0.55  fof(f35,plain,(
% 0.18/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.18/0.55    inference(resolution,[],[f25,f30])).
% 0.18/0.55  fof(f30,plain,(
% 0.18/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.18/0.55    inference(equality_resolution,[],[f27])).
% 0.18/0.55  fof(f27,plain,(
% 0.18/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.18/0.55    inference(cnf_transformation,[],[f18])).
% 0.18/0.55  fof(f25,plain,(
% 0.18/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.18/0.55    inference(cnf_transformation,[],[f13])).
% 0.18/0.55  fof(f13,plain,(
% 0.18/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.55    inference(ennf_transformation,[],[f2])).
% 0.18/0.55  fof(f2,axiom,(
% 0.18/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.18/0.55  fof(f38,plain,(
% 0.18/0.55    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) )),
% 0.18/0.55    inference(resolution,[],[f29,f19])).
% 0.18/0.55  fof(f29,plain,(
% 0.18/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f14])).
% 0.18/0.55  fof(f14,plain,(
% 0.18/0.55    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.18/0.55    inference(ennf_transformation,[],[f6])).
% 0.18/0.55  fof(f6,axiom,(
% 0.18/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 0.18/0.55  fof(f126,plain,(
% 0.18/0.55    ( ! [X0] : (r1_tarski(k8_relat_1(sK0,k8_relat_1(X0,sK2)),k8_relat_1(sK1,k8_relat_1(X0,sK2)))) )),
% 0.18/0.55    inference(superposition,[],[f49,f74])).
% 0.18/0.55  fof(f74,plain,(
% 0.18/0.55    ( ! [X0] : (k8_relat_1(sK0,k8_relat_1(sK1,k8_relat_1(X0,sK2))) = k8_relat_1(sK0,k8_relat_1(X0,sK2))) )),
% 0.18/0.55    inference(superposition,[],[f39,f34])).
% 0.18/0.55  fof(f34,plain,(
% 0.18/0.55    sK0 = k3_xboole_0(sK0,sK1)),
% 0.18/0.55    inference(resolution,[],[f25,f20])).
% 0.18/0.55  fof(f20,plain,(
% 0.18/0.55    r1_tarski(sK0,sK1)),
% 0.18/0.55    inference(cnf_transformation,[],[f16])).
% 0.18/0.55  fof(f39,plain,(
% 0.18/0.55    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,sK2))) = k8_relat_1(k3_xboole_0(X0,X1),k8_relat_1(X2,sK2))) )),
% 0.18/0.55    inference(resolution,[],[f32,f29])).
% 0.18/0.55  fof(f49,plain,(
% 0.18/0.55    ( ! [X6,X4,X5] : (r1_tarski(k8_relat_1(X4,k8_relat_1(X5,k8_relat_1(X6,sK2))),k8_relat_1(X5,k8_relat_1(X6,sK2)))) )),
% 0.18/0.55    inference(resolution,[],[f41,f24])).
% 0.18/0.55  fof(f41,plain,(
% 0.18/0.55    ( ! [X6,X5] : (v1_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK2)))) )),
% 0.18/0.55    inference(resolution,[],[f32,f23])).
% 0.18/0.55  fof(f21,plain,(
% 0.18/0.55    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.18/0.55    inference(cnf_transformation,[],[f16])).
% 0.18/0.55  % SZS output end Proof for theBenchmark
% 0.18/0.55  % (31006)------------------------------
% 0.18/0.55  % (31006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.55  % (31006)Termination reason: Refutation
% 0.18/0.55  
% 0.18/0.55  % (31006)Memory used [KB]: 1918
% 0.18/0.55  % (31006)Time elapsed: 0.140 s
% 0.18/0.55  % (31006)------------------------------
% 0.18/0.55  % (31006)------------------------------
% 0.18/0.56  % (30998)Success in time 0.21 s
%------------------------------------------------------------------------------
