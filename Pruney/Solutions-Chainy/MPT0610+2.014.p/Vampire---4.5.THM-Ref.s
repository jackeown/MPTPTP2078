%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 104 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  117 ( 344 expanded)
%              Number of equality atoms :   35 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(subsumption_resolution,[],[f235,f58])).

fof(f58,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f31,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f235,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f234,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f50,plain,(
    ! [X2] : v1_relat_1(k3_xboole_0(sK0,X2)) ),
    inference(resolution,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f234,plain,(
    k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f232,f50])).

fof(f232,plain,
    ( k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f33,f198])).

fof(f198,plain,(
    k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f192,f50])).

fof(f192,plain,
    ( k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f34,f177])).

fof(f177,plain,(
    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f110,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f110,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f109,f28])).

fof(f109,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f102,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f36,f61])).

fof(f61,plain,(
    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f33,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:48:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.46  % (2432)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.47  % (2448)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.47  % (2441)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.48  % (2441)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f236,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f235,f58])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 0.19/0.49    inference(resolution,[],[f31,f43])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.49    inference(nnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ~r1_xboole_0(sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,negated_conjecture,(
% 0.19/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.19/0.49    inference(negated_conjecture,[],[f9])).
% 0.19/0.49  fof(f9,conjecture,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 0.19/0.49  fof(f235,plain,(
% 0.19/0.49    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.19/0.49    inference(forward_demodulation,[],[f234,f67])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,X0))) )),
% 0.19/0.49    inference(resolution,[],[f50,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X2] : (v1_relat_1(k3_xboole_0(sK0,X2))) )),
% 0.19/0.49    inference(resolution,[],[f28,f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    v1_relat_1(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f234,plain,(
% 0.19/0.49    k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1))),
% 0.19/0.49    inference(subsumption_resolution,[],[f232,f50])).
% 0.19/0.49  fof(f232,plain,(
% 0.19/0.49    k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.49    inference(superposition,[],[f33,f198])).
% 0.19/0.49  fof(f198,plain,(
% 0.19/0.49    k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.49    inference(subsumption_resolution,[],[f192,f50])).
% 0.19/0.49  fof(f192,plain,(
% 0.19/0.49    k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) | ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f191])).
% 0.19/0.49  fof(f191,plain,(
% 0.19/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) | ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.49    inference(superposition,[],[f34,f177])).
% 0.19/0.49  fof(f177,plain,(
% 0.19/0.49    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.19/0.49    inference(resolution,[],[f110,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.19/0.49  fof(f110,plain,(
% 0.19/0.49    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f109,f28])).
% 0.19/0.49  fof(f109,plain,(
% 0.19/0.49    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f102,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    v1_relat_1(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f102,plain,(
% 0.19/0.49    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.19/0.49    inference(superposition,[],[f36,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.19/0.49    inference(resolution,[],[f30,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (2441)------------------------------
% 0.19/0.49  % (2441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (2441)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (2441)Memory used [KB]: 1791
% 0.19/0.49  % (2441)Time elapsed: 0.098 s
% 0.19/0.49  % (2441)------------------------------
% 0.19/0.49  % (2441)------------------------------
% 0.19/0.49  % (2430)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.49  % (2426)Success in time 0.135 s
%------------------------------------------------------------------------------
