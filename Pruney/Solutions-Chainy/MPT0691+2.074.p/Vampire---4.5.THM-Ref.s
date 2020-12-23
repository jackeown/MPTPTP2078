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
% DateTime   : Thu Dec  3 12:53:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  123 (1879 expanded)
%              Number of leaves         :   12 ( 532 expanded)
%              Depth                    :   27
%              Number of atoms          :  243 (3865 expanded)
%              Number of equality atoms :   91 (1213 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1904,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1903,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1903,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f1902,f492])).

fof(f492,plain,(
    sK0 = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f491,f48])).

fof(f48,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f47,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f491,plain,(
    k9_relat_1(k6_relat_1(sK0),sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f487,f115])).

fof(f115,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(sK0),X0) = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k9_relat_1(k6_relat_1(sK0),X0)) ),
    inference(resolution,[],[f109,f29])).

fof(f29,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) ) ),
    inference(forward_demodulation,[],[f108,f34])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(subsumption_resolution,[],[f105,f31])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f86,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f86,plain,(
    ! [X4,X2,X3] : k9_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f76,f31])).

fof(f76,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(X2,X4)) ) ),
    inference(resolution,[],[f39,f31])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f487,plain,(
    k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k9_relat_1(k6_relat_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1)))) ),
    inference(superposition,[],[f399,f86])).

fof(f399,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1)))) = k9_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1))),sK0) ),
    inference(superposition,[],[f302,f70])).

fof(f70,plain,(
    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f69,f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k10_relat_1(k6_relat_1(X0),X1) = X0 ) ),
    inference(forward_demodulation,[],[f68,f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X1) ) ),
    inference(superposition,[],[f64,f34])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,X1) ) ),
    inference(forward_demodulation,[],[f63,f33])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f302,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f292,f31])).

fof(f292,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k10_relat_1(X1,X2)) ) ),
    inference(forward_demodulation,[],[f290,f33])).

fof(f290,plain,(
    ! [X2,X1] :
      ( k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k10_relat_1(X0,k1_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k10_relat_1(X0,k1_relat_1(X1)))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f37])).

fof(f1902,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1)))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f1901,f622])).

fof(f622,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f616,f407])).

fof(f407,plain,(
    ! [X2,X3] : k9_relat_1(k6_relat_1(X3),k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(superposition,[],[f302,f86])).

fof(f616,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))) ),
    inference(resolution,[],[f609,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(subsumption_resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f609,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(forward_demodulation,[],[f608,f34])).

fof(f608,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),X0) = X0
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(forward_demodulation,[],[f607,f34])).

fof(f607,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(subsumption_resolution,[],[f599,f31])).

fof(f599,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f541,f38])).

fof(f541,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) ),
    inference(superposition,[],[f117,f407])).

fof(f117,plain,(
    ! [X4,X5] : k9_relat_1(k6_relat_1(X4),X5) = k9_relat_1(k6_relat_1(X4),k9_relat_1(k6_relat_1(X4),X5)) ),
    inference(resolution,[],[f109,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f51,f48])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f44,f33])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f35,f34])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f1901,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1900,f31])).

fof(f1900,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1898,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f1898,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f1871,f37])).

fof(f1871,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(sK0),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f623,f1352])).

fof(f1352,plain,(
    k9_relat_1(k6_relat_1(sK0),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(forward_demodulation,[],[f1347,f1323])).

fof(f1323,plain,(
    ! [X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1))))) = k9_relat_1(k6_relat_1(X1),k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1))) ),
    inference(backward_demodulation,[],[f1308,f1309])).

fof(f1309,plain,(
    ! [X2] : k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(k10_relat_1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X2),sK1)))))) = k9_relat_1(k6_relat_1(X2),k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1))) ),
    inference(superposition,[],[f622,f1300])).

fof(f1300,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)))) ),
    inference(resolution,[],[f1298,f31])).

fof(f1298,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X0,sK1)))) ) ),
    inference(subsumption_resolution,[],[f1297,f28])).

fof(f1297,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X0,sK1))))
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f1296])).

fof(f1296,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X0,sK1))))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f83,f42])).

fof(f83,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k5_relat_1(X2,sK1))
      | ~ v1_relat_1(X2)
      | k1_relat_1(k5_relat_1(X2,sK1)) = k10_relat_1(X2,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X2,sK1)))) ) ),
    inference(superposition,[],[f80,f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f1308,plain,(
    ! [X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X1),sK1)))))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1))))) ),
    inference(superposition,[],[f653,f1300])).

fof(f653,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)))) ),
    inference(backward_demodulation,[],[f633,f652])).

fof(f652,plain,(
    ! [X2,X3] : k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X2),X3)),k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) ),
    inference(forward_demodulation,[],[f617,f622])).

fof(f617,plain,(
    ! [X2,X3] : k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X2),X3)),k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3))) ),
    inference(resolution,[],[f609,f138])).

fof(f138,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f50,f133])).

fof(f133,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k6_relat_1(X4),k10_relat_1(k6_relat_1(X4),X5)) ),
    inference(resolution,[],[f114,f53])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),X2) ) ),
    inference(forward_demodulation,[],[f113,f34])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),X2)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(subsumption_resolution,[],[f110,f31])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),X2)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f95,f38])).

fof(f95,plain,(
    ! [X4,X2,X3] : k10_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k10_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f81,f31])).

fof(f81,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k10_relat_1(X2,k10_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f40,f31])).

fof(f633,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)))) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)),k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ),
    inference(backward_demodulation,[],[f530,f622])).

fof(f530,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)))) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)),k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2))) ),
    inference(superposition,[],[f407,f133])).

fof(f1347,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(superposition,[],[f653,f1304])).

fof(f1304,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f1300,f361])).

fof(f361,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(forward_demodulation,[],[f360,f48])).

fof(f360,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(sK0),sK0)) ),
    inference(subsumption_resolution,[],[f358,f31])).

fof(f358,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(sK0),sK0))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f353,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f39,f28])).

fof(f353,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),sK0) ),
    inference(superposition,[],[f294,f70])).

fof(f294,plain,(
    ! [X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(k5_relat_1(k6_relat_1(X0),sK1),k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) ),
    inference(resolution,[],[f289,f31])).

fof(f289,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,sK1)) = k9_relat_1(k5_relat_1(X0,sK1),k10_relat_1(X0,k1_relat_1(sK1))) ) ),
    inference(resolution,[],[f65,f28])).

fof(f623,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1) ),
    inference(backward_demodulation,[],[f50,f622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (16648)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (16645)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (16645)Refutation not found, incomplete strategy% (16645)------------------------------
% 0.22/0.52  % (16645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16645)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16645)Memory used [KB]: 10490
% 0.22/0.54  % (16645)Time elapsed: 0.090 s
% 0.22/0.54  % (16645)------------------------------
% 0.22/0.54  % (16645)------------------------------
% 0.22/0.54  % (16661)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.54  % (16647)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.54  % (16657)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.55  % (16665)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.55  % (16665)Refutation not found, incomplete strategy% (16665)------------------------------
% 0.22/0.55  % (16665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16665)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16665)Memory used [KB]: 10618
% 0.22/0.55  % (16665)Time elapsed: 0.076 s
% 0.22/0.55  % (16665)------------------------------
% 0.22/0.55  % (16665)------------------------------
% 0.22/0.55  % (16652)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.56  % (16652)Refutation not found, incomplete strategy% (16652)------------------------------
% 0.22/0.56  % (16652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (16652)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (16652)Memory used [KB]: 10618
% 0.22/0.56  % (16652)Time elapsed: 0.128 s
% 0.22/0.56  % (16652)------------------------------
% 0.22/0.56  % (16652)------------------------------
% 0.22/0.56  % (16642)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.56  % (16644)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.56  % (16643)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.56  % (16655)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.56  % (16649)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (16659)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.57  % (16664)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.57  % (16651)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.57  % (16650)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.57  % (16650)Refutation not found, incomplete strategy% (16650)------------------------------
% 0.22/0.57  % (16650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (16650)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (16650)Memory used [KB]: 10618
% 0.22/0.57  % (16650)Time elapsed: 0.146 s
% 0.22/0.57  % (16650)------------------------------
% 0.22/0.57  % (16650)------------------------------
% 0.22/0.58  % (16656)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.58  % (16658)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.58  % (16660)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.58  % (16663)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.58  % (16646)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.59  % (16653)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.59  % (16661)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1904,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f1903,f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f14,plain,(
% 0.22/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.59    inference(flattening,[],[f13])).
% 0.22/0.59  fof(f13,plain,(
% 0.22/0.59    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.59    inference(negated_conjecture,[],[f11])).
% 0.22/0.59  fof(f11,conjecture,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.59  fof(f1903,plain,(
% 0.22/0.59    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.59    inference(forward_demodulation,[],[f1902,f492])).
% 0.22/0.59  fof(f492,plain,(
% 0.22/0.59    sK0 = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1))))),
% 0.22/0.59    inference(forward_demodulation,[],[f491,f48])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.22/0.59    inference(forward_demodulation,[],[f47,f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f46,f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(superposition,[],[f36,f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.59  fof(f491,plain,(
% 0.22/0.59    k9_relat_1(k6_relat_1(sK0),sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1))))),
% 0.22/0.59    inference(forward_demodulation,[],[f487,f115])).
% 0.22/0.59  fof(f115,plain,(
% 0.22/0.59    ( ! [X0] : (k9_relat_1(k6_relat_1(sK0),X0) = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k9_relat_1(k6_relat_1(sK0),X0))) )),
% 0.22/0.59    inference(resolution,[],[f109,f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f109,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f108,f34])).
% 0.22/0.59  fof(f108,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f105,f31])).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(superposition,[],[f86,f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(flattening,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ( ! [X4,X2,X3] : (k9_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(k6_relat_1(X2),X4))) )),
% 0.22/0.59    inference(resolution,[],[f76,f31])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k9_relat_1(k6_relat_1(X3),k9_relat_1(X2,X4))) )),
% 0.22/0.59    inference(resolution,[],[f39,f31])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.22/0.59  fof(f487,plain,(
% 0.22/0.59    k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k9_relat_1(k6_relat_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1))))),
% 0.22/0.59    inference(superposition,[],[f399,f86])).
% 0.22/0.59  fof(f399,plain,(
% 0.22/0.59    k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1)))) = k9_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1))),sK0)),
% 0.22/0.59    inference(superposition,[],[f302,f70])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.59    inference(resolution,[],[f69,f29])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k10_relat_1(k6_relat_1(X0),X1) = X0) )),
% 0.22/0.59    inference(forward_demodulation,[],[f68,f33])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f67,f31])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.59    inference(superposition,[],[f64,f34])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,X1)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f63,f33])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f62,f31])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f60])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(superposition,[],[f37,f38])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.59  fof(f302,plain,(
% 0.22/0.59    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k10_relat_1(k6_relat_1(X1),X2))) )),
% 0.22/0.59    inference(resolution,[],[f292,f31])).
% 0.22/0.59  fof(f292,plain,(
% 0.22/0.59    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k10_relat_1(X1,X2))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f290,f33])).
% 0.22/0.59  fof(f290,plain,(
% 0.22/0.59    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(resolution,[],[f65,f31])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k10_relat_1(X0,k1_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f61,f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k10_relat_1(X0,k1_relat_1(X1))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(superposition,[],[f36,f37])).
% 0.22/0.59  fof(f1902,plain,(
% 0.22/0.59    r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1)))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.59    inference(forward_demodulation,[],[f1901,f622])).
% 0.22/0.59  fof(f622,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f616,f407])).
% 0.22/0.59  fof(f407,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X3),k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) )),
% 0.22/0.59    inference(superposition,[],[f302,f86])).
% 0.22/0.59  fof(f616,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)))) )),
% 0.22/0.59    inference(resolution,[],[f609,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f49,f31])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(resolution,[],[f41,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(flattening,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.22/0.59  fof(f609,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),X0) = X0) )),
% 0.22/0.59    inference(forward_demodulation,[],[f608,f34])).
% 0.22/0.59  fof(f608,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = X0 | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f607,f34])).
% 0.22/0.59  fof(f607,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f599,f31])).
% 0.22/0.59  fof(f599,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(superposition,[],[f541,f38])).
% 0.22/0.59  fof(f541,plain,(
% 0.22/0.59    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))) )),
% 0.22/0.59    inference(superposition,[],[f117,f407])).
% 0.22/0.59  fof(f117,plain,(
% 0.22/0.59    ( ! [X4,X5] : (k9_relat_1(k6_relat_1(X4),X5) = k9_relat_1(k6_relat_1(X4),k9_relat_1(k6_relat_1(X4),X5))) )),
% 0.22/0.59    inference(resolution,[],[f109,f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f51,f48])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0)) )),
% 0.22/0.59    inference(superposition,[],[f50,f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.22/0.59    inference(forward_demodulation,[],[f44,f33])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f43,f31])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(superposition,[],[f35,f34])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,plain,(
% 0.22/0.59    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.59  fof(f1901,plain,(
% 0.22/0.59    r1_tarski(k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.59    inference(subsumption_resolution,[],[f1900,f31])).
% 0.22/0.59  fof(f1900,plain,(
% 0.22/0.59    r1_tarski(k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.59    inference(subsumption_resolution,[],[f1898,f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    v1_relat_1(sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f1898,plain,(
% 0.22/0.59    r1_tarski(k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.59    inference(superposition,[],[f1871,f37])).
% 0.22/0.59  fof(f1871,plain,(
% 0.22/0.59    r1_tarski(k9_relat_1(k6_relat_1(sK0),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.59    inference(superposition,[],[f623,f1352])).
% 0.22/0.59  fof(f1352,plain,(
% 0.22/0.59    k9_relat_1(k6_relat_1(sK0),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 0.22/0.59    inference(forward_demodulation,[],[f1347,f1323])).
% 0.22/0.59  fof(f1323,plain,(
% 0.22/0.59    ( ! [X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1))))) = k9_relat_1(k6_relat_1(X1),k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1)))) )),
% 0.22/0.59    inference(backward_demodulation,[],[f1308,f1309])).
% 0.22/0.59  fof(f1309,plain,(
% 0.22/0.59    ( ! [X2] : (k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(k10_relat_1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X2),sK1)))))) = k9_relat_1(k6_relat_1(X2),k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)))) )),
% 0.22/0.59    inference(superposition,[],[f622,f1300])).
% 0.22/0.59  fof(f1300,plain,(
% 0.22/0.59    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1))))) )),
% 0.22/0.59    inference(resolution,[],[f1298,f31])).
% 0.22/0.59  fof(f1298,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X0,sK1))))) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f1297,f28])).
% 0.22/0.59  fof(f1297,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X0,sK1)))) | ~v1_relat_1(sK1)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f1296])).
% 0.22/0.59  fof(f1296,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X0,sK1)))) | ~v1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(resolution,[],[f83,f42])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    ( ! [X2] : (~v1_relat_1(k5_relat_1(X2,sK1)) | ~v1_relat_1(X2) | k1_relat_1(k5_relat_1(X2,sK1)) = k10_relat_1(X2,k10_relat_1(sK1,k2_relat_1(k5_relat_1(X2,sK1))))) )),
% 0.22/0.59    inference(superposition,[],[f80,f35])).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(resolution,[],[f40,f28])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.22/0.59  fof(f1308,plain,(
% 0.22/0.59    ( ! [X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X1),sK1)))))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1)))))) )),
% 0.22/0.59    inference(superposition,[],[f653,f1300])).
% 0.22/0.59  fof(f653,plain,(
% 0.22/0.59    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(k6_relat_1(X1),X2))))) )),
% 0.22/0.59    inference(backward_demodulation,[],[f633,f652])).
% 0.22/0.59  fof(f652,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X2),X3)),k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f617,f622])).
% 0.22/0.59  fof(f617,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X2),X3)),k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X3)))) )),
% 0.22/0.59    inference(resolution,[],[f609,f138])).
% 0.22/0.59  fof(f138,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),k10_relat_1(k6_relat_1(X0),X1))) )),
% 0.22/0.59    inference(superposition,[],[f50,f133])).
% 0.22/0.59  fof(f133,plain,(
% 0.22/0.59    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k10_relat_1(k6_relat_1(X4),k10_relat_1(k6_relat_1(X4),X5))) )),
% 0.22/0.59    inference(resolution,[],[f114,f53])).
% 0.22/0.59  fof(f114,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),X2)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f113,f34])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),X2) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f110,f31])).
% 0.22/0.59  fof(f110,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),X2) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(superposition,[],[f95,f38])).
% 0.22/0.59  fof(f95,plain,(
% 0.22/0.59    ( ! [X4,X2,X3] : (k10_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k10_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X3),X4))) )),
% 0.22/0.59    inference(resolution,[],[f81,f31])).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k10_relat_1(X2,k10_relat_1(k6_relat_1(X3),X4))) )),
% 0.22/0.59    inference(resolution,[],[f40,f31])).
% 0.22/0.59  fof(f633,plain,(
% 0.22/0.59    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)))) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)),k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) )),
% 0.22/0.59    inference(backward_demodulation,[],[f530,f622])).
% 0.22/0.59  fof(f530,plain,(
% 0.22/0.59    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)))) = k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)),k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)))) )),
% 0.22/0.59    inference(superposition,[],[f407,f133])).
% 0.22/0.59  fof(f1347,plain,(
% 0.22/0.59    k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),k6_relat_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 0.22/0.59    inference(superposition,[],[f653,f1304])).
% 0.22/0.59  fof(f1304,plain,(
% 0.22/0.59    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.59    inference(superposition,[],[f1300,f361])).
% 0.22/0.59  fof(f361,plain,(
% 0.22/0.59    k9_relat_1(sK1,sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 0.22/0.59    inference(forward_demodulation,[],[f360,f48])).
% 0.22/0.59  fof(f360,plain,(
% 0.22/0.59    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(sK0),sK0))),
% 0.22/0.59    inference(subsumption_resolution,[],[f358,f31])).
% 0.22/0.59  fof(f358,plain,(
% 0.22/0.59    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(sK0),sK0)) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.59    inference(superposition,[],[f353,f75])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(resolution,[],[f39,f28])).
% 0.22/0.59  fof(f353,plain,(
% 0.22/0.59    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),sK0)),
% 0.22/0.59    inference(superposition,[],[f294,f70])).
% 0.22/0.59  fof(f294,plain,(
% 0.22/0.59    ( ! [X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(k5_relat_1(k6_relat_1(X0),sK1),k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) )),
% 0.22/0.59    inference(resolution,[],[f289,f31])).
% 0.22/0.59  fof(f289,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK1)) = k9_relat_1(k5_relat_1(X0,sK1),k10_relat_1(X0,k1_relat_1(sK1)))) )),
% 0.22/0.59    inference(resolution,[],[f65,f28])).
% 0.22/0.59  fof(f623,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1)) )),
% 0.22/0.59    inference(backward_demodulation,[],[f50,f622])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (16661)------------------------------
% 0.22/0.59  % (16661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (16661)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (16661)Memory used [KB]: 7419
% 0.22/0.59  % (16661)Time elapsed: 0.161 s
% 0.22/0.59  % (16661)------------------------------
% 0.22/0.59  % (16661)------------------------------
% 0.22/0.60  % (16641)Success in time 0.234 s
%------------------------------------------------------------------------------
