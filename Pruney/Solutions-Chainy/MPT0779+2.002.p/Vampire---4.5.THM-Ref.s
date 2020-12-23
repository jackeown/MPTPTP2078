%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  61 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) ),
    inference(forward_demodulation,[],[f27,f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f15,f20])).

fof(f20,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f27,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,k3_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f14,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f19,f13])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f14,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:01:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (4013)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (4016)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.48  % (4008)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.48  % (4013)Refutation not found, incomplete strategy% (4013)------------------------------
% 0.22/0.48  % (4013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4013)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (4013)Memory used [KB]: 6140
% 0.22/0.48  % (4013)Time elapsed: 0.034 s
% 0.22/0.48  % (4013)------------------------------
% 0.22/0.48  % (4013)------------------------------
% 0.22/0.48  % (4016)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (4005)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.48  % (4006)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)),
% 0.22/0.48    inference(forward_demodulation,[],[f27,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(resolution,[],[f15,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,k3_xboole_0(sK0,sK0))),
% 0.22/0.48    inference(superposition,[],[f14,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(resolution,[],[f19,f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1)) => (k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (4016)------------------------------
% 0.22/0.48  % (4016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4016)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (4016)Memory used [KB]: 1535
% 0.22/0.48  % (4016)Time elapsed: 0.078 s
% 0.22/0.48  % (4016)------------------------------
% 0.22/0.48  % (4016)------------------------------
% 0.22/0.48  % (4010)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.48  % (4002)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (3999)Success in time 0.117 s
%------------------------------------------------------------------------------
