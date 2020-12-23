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
% DateTime   : Thu Dec  3 12:53:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 107 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 188 expanded)
%              Number of equality atoms :   44 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(subsumption_resolution,[],[f168,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

% (6434)Refutation not found, incomplete strategy% (6434)------------------------------
% (6434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f168,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f162,f82])).

fof(f82,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k3_xboole_0(X2,X3) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f78,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = k3_xboole_0(X2,X3)
      | ~ r1_tarski(k3_xboole_0(X2,X3),X2) ) ),
    inference(superposition,[],[f72,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f71,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f61,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f60,f30])).

fof(f60,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f56,f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f70,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1),X0) ),
    inference(subsumption_resolution,[],[f68,f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f62,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f162,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f28,f93])).

fof(f93,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k7_relat_1(X4,X3),X5) = k3_xboole_0(k10_relat_1(X4,X5),X3)
      | ~ v1_relat_1(X4) ) ),
    inference(forward_demodulation,[],[f92,f62])).

fof(f92,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f87,f29])).

fof(f87,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f40,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f28,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (6436)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (6427)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (6430)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (6425)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (6431)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (6434)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (6435)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (6426)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (6433)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (6438)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (6426)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f168,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2)) => (k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  % (6434)Refutation not found, incomplete strategy% (6434)------------------------------
% 0.21/0.49  % (6434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ~v1_relat_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f162,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k3_xboole_0(X2,X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k3_xboole_0(X2,X3) | ~r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.21/0.49    inference(superposition,[],[f72,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f71,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f61,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f60,f30])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f56,f29])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(superposition,[],[f32,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f70,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1),X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f68,f29])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(superposition,[],[f62,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | ~v1_relat_1(sK2)),
% 0.21/0.49    inference(superposition,[],[f28,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k10_relat_1(k7_relat_1(X4,X3),X5) = k3_xboole_0(k10_relat_1(X4,X5),X3) | ~v1_relat_1(X4)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f92,f62])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f29])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X4)) )),
% 0.21/0.49    inference(superposition,[],[f40,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (6426)------------------------------
% 0.21/0.49  % (6426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6426)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (6426)Memory used [KB]: 1663
% 0.21/0.49  % (6426)Time elapsed: 0.059 s
% 0.21/0.49  % (6426)------------------------------
% 0.21/0.49  % (6426)------------------------------
% 0.21/0.49  % (6422)Success in time 0.132 s
%------------------------------------------------------------------------------
