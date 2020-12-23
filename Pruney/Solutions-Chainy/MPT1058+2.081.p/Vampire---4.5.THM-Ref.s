%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 107 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 236 expanded)
%              Number of equality atoms :   45 (  95 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f109])).

fof(f109,plain,(
    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(superposition,[],[f57,f43])).

fof(f43,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(sK0,X1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2)) ),
    inference(forward_demodulation,[],[f42,f34])).

fof(f34,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f42,plain,(
    ! [X2,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2)) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK0),X1) = k10_relat_1(X0,k10_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f29,f20])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f57,plain,(
    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f56,f33])).

fof(f33,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f32,f24])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f31,f25])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f26,f23])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f56,plain,(
    k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f50,f40])).

fof(f40,plain,(
    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(global_subsumption,[],[f23,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f50,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[],[f46,f33])).

fof(f46,plain,(
    ! [X4,X2,X3] : k10_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X3),X4)) = k10_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4) ),
    inference(forward_demodulation,[],[f45,f35])).

fof(f35,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f27,f23])).

fof(f45,plain,(
    ! [X4,X2,X3] : k10_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k10_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f39,f23])).

fof(f39,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k10_relat_1(X2,k10_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f29,f23])).

fof(f22,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:14 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.41  % (1523)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (1528)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.19/0.42  % (1528)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f114,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(global_subsumption,[],[f22,f109])).
% 0.19/0.42  fof(f109,plain,(
% 0.19/0.42    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.19/0.42    inference(superposition,[],[f57,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(sK0,X1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2))) )),
% 0.19/0.42    inference(forward_demodulation,[],[f42,f34])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) )),
% 0.19/0.42    inference(resolution,[],[f27,f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    v1_relat_1(sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.19/0.42    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.42  fof(f8,negated_conjecture,(
% 0.19/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.19/0.42    inference(negated_conjecture,[],[f7])).
% 0.19/0.42  fof(f7,conjecture,(
% 0.19/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ( ! [X2,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2))) )),
% 0.19/0.42    inference(resolution,[],[f38,f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.42    inference(pure_predicate_removal,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK0),X1) = k10_relat_1(X0,k10_relat_1(sK0,X1))) )),
% 0.19/0.42    inference(resolution,[],[f29,f20])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))),
% 0.19/0.42    inference(forward_demodulation,[],[f56,f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.19/0.42    inference(forward_demodulation,[],[f32,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.19/0.42    inference(forward_demodulation,[],[f31,f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 0.19/0.42    inference(resolution,[],[f26,f23])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 0.19/0.42    inference(superposition,[],[f50,f40])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 0.19/0.42    inference(resolution,[],[f37,f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.42    inference(global_subsumption,[],[f23,f36])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.42    inference(superposition,[],[f28,f24])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k10_relat_1(k6_relat_1(X1),X0)) )),
% 0.19/0.42    inference(superposition,[],[f46,f33])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ( ! [X4,X2,X3] : (k10_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X3),X4)) = k10_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4)) )),
% 0.19/0.42    inference(forward_demodulation,[],[f45,f35])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.19/0.42    inference(resolution,[],[f27,f23])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    ( ! [X4,X2,X3] : (k10_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k10_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X3),X4))) )),
% 0.19/0.42    inference(resolution,[],[f39,f23])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k10_relat_1(X2,k10_relat_1(k6_relat_1(X3),X4))) )),
% 0.19/0.42    inference(resolution,[],[f29,f23])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (1528)------------------------------
% 0.19/0.42  % (1528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (1528)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (1528)Memory used [KB]: 10618
% 0.19/0.42  % (1528)Time elapsed: 0.010 s
% 0.19/0.42  % (1528)------------------------------
% 0.19/0.42  % (1528)------------------------------
% 0.19/0.43  % (1516)Success in time 0.067 s
%------------------------------------------------------------------------------
