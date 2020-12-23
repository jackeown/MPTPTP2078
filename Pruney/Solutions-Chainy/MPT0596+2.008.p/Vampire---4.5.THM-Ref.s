%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  66 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 188 expanded)
%              Number of equality atoms :   25 (  49 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106,f20])).

fof(f20,plain,(
    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
             => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

fof(f106,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f66,f57])).

fof(f57,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(resolution,[],[f52,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0)
      | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f43,f19])).

fof(f19,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK1),X1)
      | ~ r1_tarski(X1,X0)
      | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f35,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK1),X1)
      | sK1 = k5_relat_1(sK1,k6_relat_1(X1)) ) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f66,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f65,f31])).

fof(f31,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f25,f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f65,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(resolution,[],[f46,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f46,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2)) ) ),
    inference(resolution,[],[f38,f21])).

% (5723)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X1,X0),sK2) = k5_relat_1(X1,k5_relat_1(X0,sK2)) ) ),
    inference(resolution,[],[f23,f18])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.43  % (5714)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (5722)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  % (5716)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.44  % (5719)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (5718)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (5716)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f106,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.22/0.44    inference(superposition,[],[f66,f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.22/0.44    inference(resolution,[],[f52,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 0.22/0.44    inference(resolution,[],[f24,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.22/0.44    inference(resolution,[],[f43,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK1),X1) | ~r1_tarski(X1,X0) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.22/0.44    inference(resolution,[],[f35,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X1] : (~r1_tarski(k2_relat_1(sK1),X1) | sK1 = k5_relat_1(sK1,k6_relat_1(X1))) )),
% 0.22/0.44    inference(resolution,[],[f26,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f65,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 0.22/0.44    inference(resolution,[],[f25,f18])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    ( ! [X0] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),sK2))) )),
% 0.22/0.44    inference(resolution,[],[f46,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X1),sK2) = k5_relat_1(sK1,k5_relat_1(X1,sK2))) )),
% 0.22/0.44    inference(resolution,[],[f38,f21])).
% 0.22/0.44  % (5723)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X1,X0),sK2) = k5_relat_1(X1,k5_relat_1(X0,sK2))) )),
% 0.22/0.44    inference(resolution,[],[f23,f18])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (5716)------------------------------
% 0.22/0.44  % (5716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (5716)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (5716)Memory used [KB]: 10618
% 0.22/0.44  % (5716)Time elapsed: 0.008 s
% 0.22/0.44  % (5716)------------------------------
% 0.22/0.44  % (5716)------------------------------
% 0.22/0.44  % (5712)Success in time 0.076 s
%------------------------------------------------------------------------------
