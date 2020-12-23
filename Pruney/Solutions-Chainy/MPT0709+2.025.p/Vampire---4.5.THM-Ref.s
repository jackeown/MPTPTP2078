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
% DateTime   : Thu Dec  3 12:54:39 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 169 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 ( 466 expanded)
%              Number of equality atoms :   43 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(subsumption_resolution,[],[f449,f27])).

fof(f27,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f449,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f448,f213])).

fof(f213,plain,(
    sK0 = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f206,f25])).

fof(f25,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f206,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k10_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    inference(backward_demodulation,[],[f81,f202])).

fof(f202,plain,(
    ! [X2,X3] : k10_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f188,f102])).

fof(f102,plain,(
    ! [X4,X3] : k10_relat_1(k6_relat_1(X3),X4) = k9_relat_1(k6_relat_1(X3),k10_relat_1(k6_relat_1(X3),k10_relat_1(k6_relat_1(X3),X4))) ),
    inference(resolution,[],[f81,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

% (13703)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f188,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f182,f47])).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f46,f30])).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f182,plain,(
    ! [X4,X2,X3] : k9_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f67,f28])).

fof(f67,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(X2,X4)) ) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(forward_demodulation,[],[f80,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k2_relat_1(k6_relat_1(X1)))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f78,f28])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | ~ r1_tarski(X2,k2_relat_1(k6_relat_1(X1)))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f448,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f133,f400])).

fof(f400,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
    inference(subsumption_resolution,[],[f399,f41])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f399,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f382,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f382,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f316,f45])).

fof(f45,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f32,f23])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f314,f28])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2))) ) ),
    inference(superposition,[],[f35,f31])).

% (13705)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).

fof(f133,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f120,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f120,plain,(
    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) ),
    inference(superposition,[],[f63,f114])).

fof(f114,plain,(
    k9_relat_1(sK1,sK0) = k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) ),
    inference(superposition,[],[f70,f100])).

fof(f100,plain,(
    sK0 = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) ),
    inference(resolution,[],[f81,f25])).

fof(f70,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) ),
    inference(superposition,[],[f69,f45])).

fof(f69,plain,(
    ! [X2,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f66,f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f34,f23])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f62,f23])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:50:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (13690)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (13712)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (13691)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (13696)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (13690)Refutation not found, incomplete strategy% (13690)------------------------------
% 0.22/0.54  % (13690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13690)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13690)Memory used [KB]: 10618
% 0.22/0.54  % (13690)Time elapsed: 0.113 s
% 0.22/0.54  % (13690)------------------------------
% 0.22/0.54  % (13690)------------------------------
% 0.22/0.55  % (13696)Refutation not found, incomplete strategy% (13696)------------------------------
% 0.22/0.55  % (13696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13696)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13696)Memory used [KB]: 10618
% 0.22/0.55  % (13696)Time elapsed: 0.109 s
% 0.22/0.55  % (13696)------------------------------
% 0.22/0.55  % (13696)------------------------------
% 0.22/0.55  % (13694)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (13704)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (13713)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (13700)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.32/0.56  % (13714)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.56  % (13702)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.32/0.56  % (13698)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.32/0.56  % (13692)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.32/0.57  % (13706)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.32/0.57  % (13710)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.61/0.57  % (13711)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.61/0.57  % (13693)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.61/0.58  % (13695)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.61/0.58  % (13695)Refutation not found, incomplete strategy% (13695)------------------------------
% 1.61/0.58  % (13695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (13695)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (13695)Memory used [KB]: 6140
% 1.61/0.58  % (13695)Time elapsed: 0.141 s
% 1.61/0.58  % (13695)------------------------------
% 1.61/0.58  % (13695)------------------------------
% 1.61/0.58  % (13699)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.61/0.58  % (13712)Refutation found. Thanks to Tanya!
% 1.61/0.58  % SZS status Theorem for theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f450,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(subsumption_resolution,[],[f449,f27])).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.61/0.58    inference(cnf_transformation,[],[f13])).
% 1.61/0.58  fof(f13,plain,(
% 1.61/0.58    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.61/0.58    inference(flattening,[],[f12])).
% 1.61/0.58  fof(f12,plain,(
% 1.61/0.58    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.61/0.58    inference(ennf_transformation,[],[f11])).
% 1.61/0.58  fof(f11,negated_conjecture,(
% 1.61/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.61/0.58    inference(negated_conjecture,[],[f10])).
% 1.61/0.58  fof(f10,conjecture,(
% 1.61/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.61/0.58  fof(f449,plain,(
% 1.61/0.58    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.61/0.58    inference(forward_demodulation,[],[f448,f213])).
% 1.61/0.58  fof(f213,plain,(
% 1.61/0.58    sK0 = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 1.61/0.58    inference(resolution,[],[f206,f25])).
% 1.61/0.58  fof(f25,plain,(
% 1.61/0.58    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.61/0.58    inference(cnf_transformation,[],[f13])).
% 1.61/0.58  fof(f206,plain,(
% 1.61/0.58    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k10_relat_1(k6_relat_1(X1),X2) = X2) )),
% 1.61/0.58    inference(backward_demodulation,[],[f81,f202])).
% 1.61/0.58  fof(f202,plain,(
% 1.61/0.58    ( ! [X2,X3] : (k10_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3))) )),
% 1.61/0.58    inference(superposition,[],[f188,f102])).
% 1.61/0.58  fof(f102,plain,(
% 1.61/0.58    ( ! [X4,X3] : (k10_relat_1(k6_relat_1(X3),X4) = k9_relat_1(k6_relat_1(X3),k10_relat_1(k6_relat_1(X3),k10_relat_1(k6_relat_1(X3),X4)))) )),
% 1.61/0.58    inference(resolution,[],[f81,f44])).
% 1.61/0.58  fof(f44,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f43,f28])).
% 1.61/0.58  fof(f28,plain,(
% 1.61/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f6])).
% 1.61/0.58  fof(f6,axiom,(
% 1.61/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.61/0.58  fof(f43,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.61/0.58    inference(superposition,[],[f33,f30])).
% 1.61/0.58  fof(f30,plain,(
% 1.61/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.61/0.59  fof(f33,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f15])).
% 1.61/0.59  fof(f15,plain,(
% 1.61/0.59    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f3])).
% 1.61/0.59  % (13703)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.61/0.59  fof(f3,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.61/0.59  fof(f188,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1))) )),
% 1.61/0.59    inference(superposition,[],[f182,f47])).
% 1.61/0.59  fof(f47,plain,(
% 1.61/0.59    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.61/0.59    inference(forward_demodulation,[],[f46,f30])).
% 1.61/0.59  fof(f46,plain,(
% 1.61/0.59    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0))) )),
% 1.61/0.59    inference(resolution,[],[f32,f28])).
% 1.61/0.59  fof(f32,plain,(
% 1.61/0.59    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f14])).
% 1.61/0.59  fof(f14,plain,(
% 1.61/0.59    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.61/0.59    inference(ennf_transformation,[],[f5])).
% 1.61/0.59  fof(f5,axiom,(
% 1.61/0.59    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.61/0.59  fof(f182,plain,(
% 1.61/0.59    ( ! [X4,X2,X3] : (k9_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(k6_relat_1(X2),X4))) )),
% 1.61/0.59    inference(resolution,[],[f67,f28])).
% 1.61/0.59  fof(f67,plain,(
% 1.61/0.59    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(X2,X4))) )),
% 1.61/0.59    inference(resolution,[],[f34,f28])).
% 1.61/0.59  fof(f34,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f16])).
% 1.61/0.59  fof(f16,plain,(
% 1.61/0.59    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f2])).
% 1.61/0.59  fof(f2,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 1.61/0.59  fof(f81,plain,(
% 1.61/0.59    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 1.61/0.59    inference(forward_demodulation,[],[f80,f31])).
% 1.61/0.59  fof(f31,plain,(
% 1.61/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f4])).
% 1.61/0.59  fof(f80,plain,(
% 1.61/0.59    ( ! [X2,X1] : (~r1_tarski(X2,k2_relat_1(k6_relat_1(X1))) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f78,f28])).
% 1.61/0.59  fof(f78,plain,(
% 1.61/0.59    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~r1_tarski(X2,k2_relat_1(k6_relat_1(X1))) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 1.61/0.59    inference(resolution,[],[f37,f29])).
% 1.61/0.59  fof(f29,plain,(
% 1.61/0.59    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f6])).
% 1.61/0.59  fof(f37,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f22])).
% 1.61/0.59  fof(f22,plain,(
% 1.61/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(flattening,[],[f21])).
% 1.61/0.59  fof(f21,plain,(
% 1.61/0.59    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.61/0.59    inference(ennf_transformation,[],[f7])).
% 1.61/0.59  fof(f7,axiom,(
% 1.61/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.61/0.59  fof(f448,plain,(
% 1.61/0.59    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 1.61/0.59    inference(subsumption_resolution,[],[f133,f400])).
% 1.61/0.59  fof(f400,plain,(
% 1.61/0.59    ( ! [X0] : (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f399,f41])).
% 1.61/0.59  fof(f41,plain,(
% 1.61/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.61/0.59    inference(equality_resolution,[],[f39])).
% 1.61/0.59  fof(f39,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f1])).
% 1.61/0.59  fof(f1,axiom,(
% 1.61/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.59  fof(f399,plain,(
% 1.61/0.59    ( ! [X0] : (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f382,f23])).
% 1.61/0.59  fof(f23,plain,(
% 1.61/0.59    v1_relat_1(sK1)),
% 1.61/0.59    inference(cnf_transformation,[],[f13])).
% 1.61/0.59  fof(f382,plain,(
% 1.61/0.59    ( ! [X0] : (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~v1_relat_1(sK1) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))) )),
% 1.61/0.59    inference(superposition,[],[f316,f45])).
% 1.61/0.59  fof(f45,plain,(
% 1.61/0.59    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 1.61/0.59    inference(resolution,[],[f32,f23])).
% 1.61/0.59  fof(f316,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2))) | ~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1))) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f314,f28])).
% 1.61/0.59  fof(f314,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2)))) )),
% 1.61/0.59    inference(superposition,[],[f35,f31])).
% 1.61/0.59  % (13705)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.61/0.59  fof(f35,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f18])).
% 1.61/0.59  fof(f18,plain,(
% 1.61/0.59    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(flattening,[],[f17])).
% 1.61/0.59  fof(f17,plain,(
% 1.61/0.59    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f9])).
% 1.61/0.59  fof(f9,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).
% 1.61/0.59  fof(f133,plain,(
% 1.61/0.59    ~r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 1.61/0.59    inference(resolution,[],[f120,f40])).
% 1.61/0.59  fof(f40,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f1])).
% 1.61/0.59  fof(f120,plain,(
% 1.61/0.59    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0))),
% 1.61/0.59    inference(superposition,[],[f63,f114])).
% 1.61/0.59  fof(f114,plain,(
% 1.61/0.59    k9_relat_1(sK1,sK0) = k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0))),
% 1.61/0.59    inference(superposition,[],[f70,f100])).
% 1.61/0.59  fof(f100,plain,(
% 1.61/0.59    sK0 = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0))),
% 1.61/0.59    inference(resolution,[],[f81,f25])).
% 1.61/0.59  fof(f70,plain,(
% 1.61/0.59    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0))) )),
% 1.61/0.59    inference(superposition,[],[f69,f45])).
% 1.61/0.59  fof(f69,plain,(
% 1.61/0.59    ( ! [X2,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(X1),X2))) )),
% 1.61/0.59    inference(resolution,[],[f66,f28])).
% 1.61/0.59  fof(f66,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1))) )),
% 1.61/0.59    inference(resolution,[],[f34,f23])).
% 1.61/0.59  fof(f63,plain,(
% 1.61/0.59    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f62,f23])).
% 1.61/0.59  fof(f62,plain,(
% 1.61/0.59    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.61/0.59    inference(subsumption_resolution,[],[f61,f24])).
% 1.61/0.59  fof(f24,plain,(
% 1.61/0.59    v1_funct_1(sK1)),
% 1.61/0.59    inference(cnf_transformation,[],[f13])).
% 1.61/0.59  fof(f61,plain,(
% 1.61/0.59    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.61/0.59    inference(resolution,[],[f36,f26])).
% 1.61/0.59  fof(f26,plain,(
% 1.61/0.59    v2_funct_1(sK1)),
% 1.61/0.59    inference(cnf_transformation,[],[f13])).
% 1.61/0.59  fof(f36,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f20])).
% 1.61/0.59  fof(f20,plain,(
% 1.61/0.59    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(flattening,[],[f19])).
% 1.61/0.59  fof(f19,plain,(
% 1.61/0.59    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.61/0.59    inference(ennf_transformation,[],[f8])).
% 1.61/0.59  fof(f8,axiom,(
% 1.61/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.61/0.59  % SZS output end Proof for theBenchmark
% 1.61/0.59  % (13712)------------------------------
% 1.61/0.59  % (13712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (13712)Termination reason: Refutation
% 1.61/0.59  
% 1.61/0.59  % (13712)Memory used [KB]: 11001
% 1.61/0.59  % (13712)Time elapsed: 0.148 s
% 1.61/0.59  % (13712)------------------------------
% 1.61/0.59  % (13712)------------------------------
% 1.61/0.59  % (13703)Refutation not found, incomplete strategy% (13703)------------------------------
% 1.61/0.59  % (13703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (13703)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (13703)Memory used [KB]: 6140
% 1.61/0.59  % (13703)Time elapsed: 0.156 s
% 1.61/0.59  % (13703)------------------------------
% 1.61/0.59  % (13703)------------------------------
% 1.61/0.59  % (13689)Success in time 0.223 s
%------------------------------------------------------------------------------
