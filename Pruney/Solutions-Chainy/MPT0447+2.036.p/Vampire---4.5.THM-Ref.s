%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 124 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 466 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f19,f226])).

fof(f226,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f95,f54])).

fof(f54,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(sK1))
      | ~ r1_tarski(X2,sK1)
      | ~ v1_relat_1(X2) ) ),
    inference(global_subsumption,[],[f20,f53])).

fof(f53,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(sK1))
      | ~ r1_tarski(X2,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f42,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k1_relat_1(sK1))
      | r1_tarski(X7,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f29,f32])).

fof(f32,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f23,f20])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f95,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(global_subsumption,[],[f22,f21,f19,f93])).

fof(f93,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_relat_1(sK0),X6)
      | r1_tarski(k3_relat_1(sK0),X6)
      | ~ r1_tarski(k1_relat_1(sK0),X6) ) ),
    inference(superposition,[],[f28,f31])).

fof(f31,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f23,f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f48,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(X2),k3_relat_1(sK1))
      | ~ r1_tarski(X2,sK1)
      | ~ v1_relat_1(X2) ) ),
    inference(global_subsumption,[],[f20,f47])).

fof(f47,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(X2),k3_relat_1(sK1))
      | ~ r1_tarski(X2,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f27,f32])).

fof(f22,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (31289)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  % (31284)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (31283)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (31281)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (31289)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f227,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f21,f19,f226])).
% 0.21/0.43  fof(f226,plain,(
% 0.21/0.43    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 0.21/0.43    inference(resolution,[],[f95,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(sK1)) | ~r1_tarski(X2,sK1) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(global_subsumption,[],[f20,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(sK1)) | ~r1_tarski(X2,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(resolution,[],[f42,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X7] : (~r1_tarski(X7,k1_relat_1(sK1)) | r1_tarski(X7,k3_relat_1(sK1))) )),
% 0.21/0.43    inference(superposition,[],[f29,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f23,f20])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 0.21/0.43    inference(superposition,[],[f27,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.43    inference(global_subsumption,[],[f22,f21,f19,f93])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f48,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X6] : (~r1_tarski(k2_relat_1(sK0),X6) | r1_tarski(k3_relat_1(sK0),X6) | ~r1_tarski(k1_relat_1(sK0),X6)) )),
% 0.21/0.43    inference(superposition,[],[f28,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.43    inference(resolution,[],[f23,f19])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X2] : (r1_tarski(k2_relat_1(X2),k3_relat_1(sK1)) | ~r1_tarski(X2,sK1) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(global_subsumption,[],[f20,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X2] : (r1_tarski(k2_relat_1(X2),k3_relat_1(sK1)) | ~r1_tarski(X2,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(resolution,[],[f38,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X1] : (~r1_tarski(X1,k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 0.21/0.43    inference(superposition,[],[f27,f32])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (31289)------------------------------
% 0.21/0.43  % (31289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (31289)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (31289)Memory used [KB]: 10746
% 0.21/0.43  % (31289)Time elapsed: 0.012 s
% 0.21/0.43  % (31289)------------------------------
% 0.21/0.43  % (31289)------------------------------
% 0.21/0.44  % (31273)Success in time 0.077 s
%------------------------------------------------------------------------------
