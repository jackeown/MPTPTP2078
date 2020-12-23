%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 107 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 218 expanded)
%              Number of equality atoms :   43 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f167,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f167,plain,(
    ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f164,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(f164,plain,(
    k2_wellord1(sK1,sK0) != k7_relat_1(k8_relat_1(sK0,sK1),sK0) ),
    inference(superposition,[],[f25,f163])).

fof(f163,plain,(
    ! [X2,X1] : k8_relat_1(X1,k7_relat_1(sK1,X2)) = k7_relat_1(k8_relat_1(X1,sK1),X2) ),
    inference(backward_demodulation,[],[f63,f162])).

fof(f162,plain,(
    ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) ),
    inference(subsumption_resolution,[],[f161,f24])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f158,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f158,plain,(
    ! [X2,X1] : k5_relat_1(k6_relat_1(X1),k5_relat_1(sK1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X2,sK1),X1) ),
    inference(forward_demodulation,[],[f157,f111])).

fof(f111,plain,(
    ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f110,f24])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f106,f30])).

fof(f106,plain,(
    ! [X0,X1] : k7_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X0)) ),
    inference(resolution,[],[f74,f24])).

fof(f74,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(X2,X4),k6_relat_1(X3)) ) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f157,plain,(
    ! [X2,X1] : k5_relat_1(k6_relat_1(X1),k5_relat_1(sK1,k6_relat_1(X2))) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f156,f42])).

fof(f42,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f31,f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

% (19833)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f156,plain,(
    ! [X2,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(sK1,k6_relat_1(X2))) ),
    inference(resolution,[],[f118,f27])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,sK1),k6_relat_1(X1)) = k5_relat_1(X0,k5_relat_1(sK1,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f86,f24])).

fof(f86,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,X3),k6_relat_1(X4)) = k5_relat_1(X2,k5_relat_1(X3,k6_relat_1(X4)))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f63,plain,(
    ! [X2,X1] : k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,sK1)) = k8_relat_1(X1,k7_relat_1(sK1,X2)) ),
    inference(forward_demodulation,[],[f62,f42])).

fof(f62,plain,(
    ! [X2,X1] : k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),sK1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,sK1)) ),
    inference(resolution,[],[f58,f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,k5_relat_1(X1,sK1)) = k5_relat_1(X1,k8_relat_1(X0,sK1)) ) ),
    inference(resolution,[],[f33,f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f25,plain,(
    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.48  % (19809)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.48  % (19826)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.49  % (19817)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (19817)Refutation not found, incomplete strategy% (19817)------------------------------
% 0.21/0.49  % (19817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19807)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (19809)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (19817)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19817)Memory used [KB]: 10618
% 0.21/0.50  % (19817)Time elapsed: 0.096 s
% 0.21/0.50  % (19817)------------------------------
% 0.21/0.50  % (19817)------------------------------
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0,X1] : (k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0)) & v1_relat_1(X1)) => (k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1] : (k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ~v1_relat_1(sK1)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.21/0.50    inference(superposition,[],[f164,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    k2_wellord1(sK1,sK0) != k7_relat_1(k8_relat_1(sK0,sK1),sK0)),
% 0.21/0.50    inference(superposition,[],[f25,f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k8_relat_1(X1,k7_relat_1(sK1,X2)) = k7_relat_1(k8_relat_1(X1,sK1),X2)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f63,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f24])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.50    inference(superposition,[],[f158,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X1),k5_relat_1(sK1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X2,sK1),X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f157,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f24])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.50    inference(superposition,[],[f106,f30])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f74,f24])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(X2,X4),k6_relat_1(X3))) )),
% 0.21/0.50    inference(resolution,[],[f34,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X1),k5_relat_1(sK1,k6_relat_1(X2))) = k5_relat_1(k7_relat_1(sK1,X1),k6_relat_1(X2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f156,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.21/0.50    inference(resolution,[],[f31,f24])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.50  % (19833)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(sK1,k6_relat_1(X2)))) )),
% 0.21/0.50    inference(resolution,[],[f118,f27])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,sK1),k6_relat_1(X1)) = k5_relat_1(X0,k5_relat_1(sK1,k6_relat_1(X1)))) )),
% 0.21/0.50    inference(resolution,[],[f86,f24])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,X3),k6_relat_1(X4)) = k5_relat_1(X2,k5_relat_1(X3,k6_relat_1(X4))) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(resolution,[],[f29,f27])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,sK1)) = k8_relat_1(X1,k7_relat_1(sK1,X2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f62,f42])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),sK1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,sK1))) )),
% 0.21/0.50    inference(resolution,[],[f58,f27])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,k5_relat_1(X1,sK1)) = k5_relat_1(X1,k8_relat_1(X0,sK1))) )),
% 0.21/0.50    inference(resolution,[],[f33,f24])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (19809)------------------------------
% 0.21/0.50  % (19809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19809)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (19809)Memory used [KB]: 10874
% 0.21/0.50  % (19809)Time elapsed: 0.097 s
% 0.21/0.50  % (19809)------------------------------
% 0.21/0.50  % (19809)------------------------------
% 0.21/0.50  % (19803)Success in time 0.144 s
%------------------------------------------------------------------------------
