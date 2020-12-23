%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 192 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 469 expanded)
%              Number of equality atoms :   55 ( 161 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(global_subsumption,[],[f27,f83])).

fof(f83,plain,(
    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f81,f52])).

fof(f52,plain,(
    k10_relat_1(sK0,sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(forward_demodulation,[],[f51,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f51,plain,(
    k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f44,f49])).

fof(f49,plain,(
    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f26,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(global_subsumption,[],[f30,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f36,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f44,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f81,plain,(
    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(superposition,[],[f80,f55])).

fof(f55,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f53,f29])).

fof(f29,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f53,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k2_funct_1(k6_relat_1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f30,f31,f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f28,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f31,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,(
    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(superposition,[],[f79,f49])).

fof(f79,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k10_relat_1(k7_relat_1(sK0,X0),sK2) ),
    inference(forward_demodulation,[],[f76,f68])).

fof(f68,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(forward_demodulation,[],[f67,f39])).

fof(f39,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(forward_demodulation,[],[f58,f55])).

fof(f58,plain,(
    ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f30,f24,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f76,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f65,f52])).

fof(f65,plain,(
    ! [X2,X0,X1] : k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f64,f40])).

fof(f40,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f30,f34])).

fof(f64,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(forward_demodulation,[],[f63,f55])).

fof(f63,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(forward_demodulation,[],[f60,f55])).

fof(f60,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(unit_resulting_resolution,[],[f30,f30,f37])).

fof(f27,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (2112)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.49  % (2112)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(global_subsumption,[],[f27,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f81,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    k10_relat_1(sK0,sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 0.20/0.49    inference(forward_demodulation,[],[f51,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 0.20/0.49    inference(superposition,[],[f44,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f26,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(global_subsumption,[],[f30,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f36,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f30,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 0.20/0.49    inference(superposition,[],[f80,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f53,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k2_funct_1(k6_relat_1(X0)),X1)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f30,f31,f28,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 0.20/0.49    inference(superposition,[],[f79,f49])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0] : (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k10_relat_1(k7_relat_1(sK0,X0),sK2)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f76,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f67,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f24,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f58,f55])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f30,f24,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0] : (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2))) )),
% 0.20/0.49    inference(superposition,[],[f65,f52])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f64,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f30,f34])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X2))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f63,f55])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f60,f55])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2))) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f30,f30,f37])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (2112)------------------------------
% 0.20/0.49  % (2112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2112)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (2112)Memory used [KB]: 10618
% 0.20/0.49  % (2112)Time elapsed: 0.037 s
% 0.20/0.49  % (2112)------------------------------
% 0.20/0.49  % (2112)------------------------------
% 0.20/0.49  % (2102)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (2096)Success in time 0.13 s
%------------------------------------------------------------------------------
