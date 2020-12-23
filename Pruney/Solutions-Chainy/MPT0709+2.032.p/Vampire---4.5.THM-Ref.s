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
% DateTime   : Thu Dec  3 12:54:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 271 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  194 (1152 expanded)
%              Number of equality atoms :   55 ( 240 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f362,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f34])).

fof(f34,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f358,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f327,f32])).

fof(f32,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f327,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X6)) = X6 ) ),
    inference(backward_demodulation,[],[f92,f324])).

fof(f324,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f133,f323])).

fof(f323,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f209,f176])).

fof(f176,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    inference(superposition,[],[f85,f48])).

fof(f48,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X2] : r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(k2_funct_1(sK1))) ),
    inference(forward_demodulation,[],[f77,f61])).

fof(f61,plain,(
    ! [X4] : k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4) ),
    inference(subsumption_resolution,[],[f60,f31])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X4] :
      ( k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f33,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X4] :
      ( k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f77,plain,(
    ! [X2] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X2),k1_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f58,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f51,f31])).

fof(f51,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f209,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | k1_relat_1(sK1) = k10_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f204,f30])).

fof(f204,plain,(
    ! [X0] :
      ( k1_relat_1(sK1) = k10_relat_1(sK1,X0)
      | ~ r1_tarski(k2_relat_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f150,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f150,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f145,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f145,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f133,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f129,f58])).

fof(f129,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f63,f39])).

fof(f63,plain,(
    ! [X5] : k10_relat_1(sK1,X5) = k9_relat_1(k2_funct_1(sK1),X5) ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X5] :
      ( k10_relat_1(sK1,X5) = k9_relat_1(k2_funct_1(sK1),X5)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X5] :
      ( k10_relat_1(sK1,X5) = k9_relat_1(k2_funct_1(sK1),X5)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f92,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k2_relat_1(k2_funct_1(sK1)))
      | k10_relat_1(sK1,k9_relat_1(sK1,X6)) = X6 ) ),
    inference(forward_demodulation,[],[f91,f61])).

fof(f91,plain,(
    ! [X6] :
      ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X6)) = X6
      | ~ r1_tarski(X6,k2_relat_1(k2_funct_1(sK1))) ) ),
    inference(forward_demodulation,[],[f90,f63])).

fof(f90,plain,(
    ! [X6] :
      ( k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X6)) = X6
      | ~ r1_tarski(X6,k2_relat_1(k2_funct_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f81,f59])).

fof(f59,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f52,f31])).

fof(f52,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X6] :
      ( k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X6)) = X6
      | ~ r1_tarski(X6,k2_relat_1(k2_funct_1(sK1)))
      | ~ v1_funct_1(k2_funct_1(sK1)) ) ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (3121)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.46  % (3129)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.47  % (3121)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f358,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.21/0.48    inference(resolution,[],[f327,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    ( ! [X6] : (~r1_tarski(X6,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X6)) = X6) )),
% 0.21/0.48    inference(backward_demodulation,[],[f92,f324])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    inference(backward_demodulation,[],[f133,f323])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    k1_relat_1(sK1) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))),
% 0.21/0.48    inference(resolution,[],[f209,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.21/0.48    inference(superposition,[],[f85,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f30,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2] : (r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(k2_funct_1(sK1)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f77,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X4] : (k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X4] : (k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4) | ~v1_funct_1(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v2_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X4] : (k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)) )),
% 0.21/0.48    inference(resolution,[],[f30,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X2] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X2),k1_relat_1(k2_funct_1(sK1)))) )),
% 0.21/0.48    inference(resolution,[],[f58,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f51,f31])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f30,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | k1_relat_1(sK1) = k10_relat_1(sK1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f204,f30])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(sK1) = k10_relat_1(sK1,X0) | ~r1_tarski(k2_relat_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.48    inference(superposition,[],[f150,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(sK1,X0) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f145,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X0)))) )),
% 0.21/0.48    inference(resolution,[],[f49,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f30,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f58])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    inference(superposition,[],[f63,f39])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X5] : (k10_relat_1(sK1,X5) = k9_relat_1(k2_funct_1(sK1),X5)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f31])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X5] : (k10_relat_1(sK1,X5) = k9_relat_1(k2_funct_1(sK1),X5) | ~v1_funct_1(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f33])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X5] : (k10_relat_1(sK1,X5) = k9_relat_1(k2_funct_1(sK1),X5) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)) )),
% 0.21/0.48    inference(resolution,[],[f30,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X6] : (~r1_tarski(X6,k2_relat_1(k2_funct_1(sK1))) | k10_relat_1(sK1,k9_relat_1(sK1,X6)) = X6) )),
% 0.21/0.48    inference(forward_demodulation,[],[f91,f61])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X6] : (k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X6)) = X6 | ~r1_tarski(X6,k2_relat_1(k2_funct_1(sK1)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f90,f63])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X6] : (k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X6)) = X6 | ~r1_tarski(X6,k2_relat_1(k2_funct_1(sK1)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f52,f31])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f30,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X6] : (k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X6)) = X6 | ~r1_tarski(X6,k2_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1))) )),
% 0.21/0.48    inference(resolution,[],[f58,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3121)------------------------------
% 0.21/0.48  % (3121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3121)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3121)Memory used [KB]: 1918
% 0.21/0.48  % (3121)Time elapsed: 0.056 s
% 0.21/0.48  % (3121)------------------------------
% 0.21/0.48  % (3121)------------------------------
% 0.21/0.48  % (3109)Success in time 0.123 s
%------------------------------------------------------------------------------
