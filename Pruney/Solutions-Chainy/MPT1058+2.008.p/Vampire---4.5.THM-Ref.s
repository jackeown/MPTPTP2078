%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:18 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 250 expanded)
%              Number of leaves         :   17 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  181 ( 588 expanded)
%              Number of equality atoms :   60 ( 218 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f872,plain,(
    $false ),
    inference(subsumption_resolution,[],[f871,f137])).

fof(f137,plain,(
    ! [X4,X3] : r1_tarski(k10_relat_1(k7_relat_1(sK0,X3),X4),k10_relat_1(sK0,X4)) ),
    inference(subsumption_resolution,[],[f135,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK0,X0),sK0) ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f135,plain,(
    ! [X4,X3] :
      ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X3),X4),k10_relat_1(sK0,X4))
      | ~ r1_tarski(k7_relat_1(sK0,X3),sK0) ) ),
    inference(resolution,[],[f109,f71])).

fof(f71,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f54,f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(sK0,X1))
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f62,f44])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(f871,plain,(
    ~ r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f870,f142])).

fof(f142,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(sK0,X1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2)) ),
    inference(forward_demodulation,[],[f139,f86])).

fof(f86,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    inference(resolution,[],[f57,f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f139,plain,(
    ! [X2,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2)) ),
    inference(resolution,[],[f112,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK0),X1) = k10_relat_1(X0,k10_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f870,plain,(
    ~ r1_tarski(k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f869,f847])).

fof(f847,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f264,f173])).

fof(f173,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f77,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f264,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f260,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f260,plain,(
    k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f91,f190])).

fof(f190,plain,(
    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f103,f45])).

fof(f45,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f101,f48])).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f60,f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f91,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f48,f89])).

fof(f89,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f53,f87])).

fof(f87,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f57,f47])).

fof(f53,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f869,plain,(
    ~ r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f868,f46])).

fof(f46,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f868,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f863,f142])).

fof(f863,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))
    | ~ r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f294,f847])).

fof(f294,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f198,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f198,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))) ),
    inference(resolution,[],[f108,f45])).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k3_xboole_0(X2,X1))) ) ),
    inference(forward_demodulation,[],[f107,f99])).

fof(f99,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(forward_demodulation,[],[f97,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f49,f89])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f58,f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X1))) ) ),
    inference(forward_demodulation,[],[f105,f48])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X2)))
      | r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X1))) ) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:02:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3566)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (3555)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (3551)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (3561)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (3559)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (3560)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (3574)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (3553)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (3554)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (3573)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (3569)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (3556)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (3571)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (3580)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (3578)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (3557)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (3552)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (3576)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (3572)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.55  % (3558)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.55  % (3570)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.55  % (3563)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.29/0.55  % (3577)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.56  % (3568)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.29/0.56  % (3564)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.29/0.56  % (3565)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.56  % (3562)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.56  % (3579)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.29/0.56  % (3575)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.57  % (3567)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.61  % (3558)Refutation found. Thanks to Tanya!
% 1.57/0.61  % SZS status Theorem for theBenchmark
% 1.57/0.61  % SZS output start Proof for theBenchmark
% 1.57/0.61  fof(f872,plain,(
% 1.57/0.61    $false),
% 1.57/0.61    inference(subsumption_resolution,[],[f871,f137])).
% 1.57/0.61  fof(f137,plain,(
% 1.57/0.61    ( ! [X4,X3] : (r1_tarski(k10_relat_1(k7_relat_1(sK0,X3),X4),k10_relat_1(sK0,X4))) )),
% 1.57/0.61    inference(subsumption_resolution,[],[f135,f73])).
% 1.57/0.61  fof(f73,plain,(
% 1.57/0.61    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),sK0)) )),
% 1.57/0.61    inference(resolution,[],[f55,f44])).
% 1.57/0.61  fof(f44,plain,(
% 1.57/0.61    v1_relat_1(sK0)),
% 1.57/0.61    inference(cnf_transformation,[],[f41])).
% 1.57/0.61  fof(f41,plain,(
% 1.57/0.61    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 1.57/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f40,f39])).
% 1.57/0.61  fof(f39,plain,(
% 1.57/0.61    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 1.57/0.61    introduced(choice_axiom,[])).
% 1.57/0.61  fof(f40,plain,(
% 1.57/0.61    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.57/0.61    introduced(choice_axiom,[])).
% 1.57/0.61  fof(f24,plain,(
% 1.57/0.61    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 1.57/0.61    inference(ennf_transformation,[],[f22])).
% 1.57/0.61  fof(f22,plain,(
% 1.57/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.57/0.61    inference(pure_predicate_removal,[],[f21])).
% 1.57/0.61  fof(f21,negated_conjecture,(
% 1.57/0.61    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.57/0.61    inference(negated_conjecture,[],[f20])).
% 1.57/0.61  fof(f20,conjecture,(
% 1.57/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.57/0.61  fof(f55,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f26])).
% 1.57/0.61  fof(f26,plain,(
% 1.57/0.61    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f14])).
% 1.57/0.61  fof(f14,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.57/0.61  fof(f135,plain,(
% 1.57/0.61    ( ! [X4,X3] : (r1_tarski(k10_relat_1(k7_relat_1(sK0,X3),X4),k10_relat_1(sK0,X4)) | ~r1_tarski(k7_relat_1(sK0,X3),sK0)) )),
% 1.57/0.61    inference(resolution,[],[f109,f71])).
% 1.57/0.61  fof(f71,plain,(
% 1.57/0.61    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) )),
% 1.57/0.61    inference(resolution,[],[f54,f44])).
% 1.57/0.61  fof(f54,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f25])).
% 1.57/0.61  fof(f25,plain,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.57/0.61    inference(ennf_transformation,[],[f8])).
% 1.57/0.61  fof(f8,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.57/0.61  fof(f109,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(sK0,X1)) | ~r1_tarski(X0,sK0)) )),
% 1.57/0.61    inference(resolution,[],[f62,f44])).
% 1.57/0.61  fof(f62,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X1,X2) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f36])).
% 1.57/0.61  fof(f36,plain,(
% 1.57/0.61    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(flattening,[],[f35])).
% 1.57/0.61  fof(f35,plain,(
% 1.57/0.61    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f10])).
% 1.57/0.61  fof(f10,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).
% 1.57/0.61  fof(f871,plain,(
% 1.57/0.61    ~r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2))),
% 1.57/0.61    inference(forward_demodulation,[],[f870,f142])).
% 1.57/0.61  fof(f142,plain,(
% 1.57/0.61    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(sK0,X1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2))) )),
% 1.57/0.61    inference(forward_demodulation,[],[f139,f86])).
% 1.57/0.61  fof(f86,plain,(
% 1.57/0.61    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) )),
% 1.57/0.61    inference(resolution,[],[f57,f44])).
% 1.57/0.61  fof(f57,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f28])).
% 1.57/0.61  fof(f28,plain,(
% 1.57/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f15])).
% 1.57/0.61  fof(f15,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.57/0.61  fof(f139,plain,(
% 1.57/0.61    ( ! [X2,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2))) )),
% 1.57/0.61    inference(resolution,[],[f112,f47])).
% 1.57/0.61  fof(f47,plain,(
% 1.57/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f23])).
% 1.57/0.61  fof(f23,plain,(
% 1.57/0.61    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.57/0.61    inference(pure_predicate_removal,[],[f17])).
% 1.57/0.61  fof(f17,axiom,(
% 1.57/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.57/0.61  fof(f112,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK0),X1) = k10_relat_1(X0,k10_relat_1(sK0,X1))) )),
% 1.57/0.61    inference(resolution,[],[f61,f44])).
% 1.57/0.61  fof(f61,plain,(
% 1.57/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f34])).
% 1.57/0.61  fof(f34,plain,(
% 1.57/0.61    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f11])).
% 1.57/0.61  fof(f11,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 1.57/0.61  fof(f870,plain,(
% 1.57/0.61    ~r1_tarski(k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.57/0.61    inference(forward_demodulation,[],[f869,f847])).
% 1.57/0.61  fof(f847,plain,(
% 1.57/0.61    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.57/0.61    inference(superposition,[],[f264,f173])).
% 1.57/0.61  fof(f173,plain,(
% 1.57/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.57/0.61    inference(superposition,[],[f77,f52])).
% 1.57/0.61  fof(f52,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f7])).
% 1.57/0.61  fof(f7,axiom,(
% 1.57/0.61    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.57/0.61  fof(f77,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.57/0.61    inference(superposition,[],[f52,f50])).
% 1.57/0.61  fof(f50,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f3])).
% 1.57/0.61  fof(f3,axiom,(
% 1.57/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.57/0.61  fof(f264,plain,(
% 1.57/0.61    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 1.57/0.61    inference(forward_demodulation,[],[f260,f48])).
% 1.57/0.61  fof(f48,plain,(
% 1.57/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.57/0.61    inference(cnf_transformation,[],[f12])).
% 1.57/0.61  fof(f12,axiom,(
% 1.57/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.57/0.61  fof(f260,plain,(
% 1.57/0.61    k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.57/0.61    inference(superposition,[],[f91,f190])).
% 1.57/0.61  fof(f190,plain,(
% 1.57/0.61    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.57/0.61    inference(resolution,[],[f103,f45])).
% 1.57/0.61  fof(f45,plain,(
% 1.57/0.61    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.57/0.61    inference(cnf_transformation,[],[f41])).
% 1.57/0.61  fof(f103,plain,(
% 1.57/0.61    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.57/0.61    inference(forward_demodulation,[],[f101,f48])).
% 1.57/0.61  fof(f101,plain,(
% 1.57/0.61    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.57/0.61    inference(resolution,[],[f60,f47])).
% 1.57/0.61  fof(f60,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.57/0.61    inference(cnf_transformation,[],[f33])).
% 1.57/0.61  fof(f33,plain,(
% 1.57/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(flattening,[],[f32])).
% 1.57/0.61  fof(f32,plain,(
% 1.57/0.61    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f16])).
% 1.57/0.61  fof(f16,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.57/0.61  fof(f91,plain,(
% 1.57/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 1.57/0.61    inference(superposition,[],[f48,f89])).
% 1.57/0.61  fof(f89,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.57/0.61    inference(backward_demodulation,[],[f53,f87])).
% 1.57/0.61  fof(f87,plain,(
% 1.57/0.61    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.57/0.61    inference(resolution,[],[f57,f47])).
% 1.57/0.61  fof(f53,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f19])).
% 1.57/0.61  fof(f19,axiom,(
% 1.57/0.61    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.57/0.61  fof(f869,plain,(
% 1.57/0.61    ~r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))),
% 1.57/0.61    inference(subsumption_resolution,[],[f868,f46])).
% 1.57/0.61  fof(f46,plain,(
% 1.57/0.61    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.57/0.61    inference(cnf_transformation,[],[f41])).
% 1.57/0.61  fof(f868,plain,(
% 1.57/0.61    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | ~r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))),
% 1.57/0.61    inference(forward_demodulation,[],[f863,f142])).
% 1.57/0.61  fof(f863,plain,(
% 1.57/0.61    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) | ~r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))),
% 1.57/0.61    inference(backward_demodulation,[],[f294,f847])).
% 1.57/0.61  fof(f294,plain,(
% 1.57/0.61    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~r1_tarski(k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),k10_relat_1(sK0,sK2))),
% 1.57/0.61    inference(resolution,[],[f198,f65])).
% 1.57/0.61  fof(f65,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f43])).
% 1.57/0.61  fof(f43,plain,(
% 1.57/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.61    inference(flattening,[],[f42])).
% 1.57/0.61  fof(f42,plain,(
% 1.57/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.61    inference(nnf_transformation,[],[f1])).
% 1.57/0.61  fof(f1,axiom,(
% 1.57/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.61  fof(f198,plain,(
% 1.57/0.61    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))))),
% 1.57/0.61    inference(resolution,[],[f108,f45])).
% 1.57/0.61  fof(f108,plain,(
% 1.57/0.61    ( ! [X2,X1] : (~r1_tarski(X1,X2) | r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k3_xboole_0(X2,X1)))) )),
% 1.57/0.61    inference(forward_demodulation,[],[f107,f99])).
% 1.57/0.61  fof(f99,plain,(
% 1.57/0.61    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.57/0.61    inference(forward_demodulation,[],[f97,f90])).
% 1.57/0.61  fof(f90,plain,(
% 1.57/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.57/0.61    inference(superposition,[],[f49,f89])).
% 1.57/0.61  fof(f49,plain,(
% 1.57/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.57/0.61    inference(cnf_transformation,[],[f12])).
% 1.57/0.61  fof(f97,plain,(
% 1.57/0.61    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.57/0.61    inference(resolution,[],[f58,f47])).
% 1.57/0.61  fof(f58,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.57/0.61    inference(cnf_transformation,[],[f29])).
% 1.57/0.61  fof(f29,plain,(
% 1.57/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f9])).
% 1.57/0.61  fof(f9,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.57/0.61  fof(f107,plain,(
% 1.57/0.61    ( ! [X2,X1] : (~r1_tarski(X1,X2) | r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X1)))) )),
% 1.57/0.61    inference(forward_demodulation,[],[f105,f48])).
% 1.57/0.61  fof(f105,plain,(
% 1.57/0.61    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(k6_relat_1(X2))) | r1_tarski(X1,k10_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X1)))) )),
% 1.57/0.61    inference(resolution,[],[f59,f47])).
% 1.57/0.61  fof(f59,plain,(
% 1.57/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 1.57/0.61    inference(cnf_transformation,[],[f31])).
% 1.57/0.61  fof(f31,plain,(
% 1.57/0.61    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(flattening,[],[f30])).
% 1.57/0.61  fof(f30,plain,(
% 1.57/0.61    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.57/0.61    inference(ennf_transformation,[],[f18])).
% 1.57/0.61  fof(f18,axiom,(
% 1.57/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.57/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.57/0.61  % SZS output end Proof for theBenchmark
% 1.57/0.61  % (3558)------------------------------
% 1.57/0.61  % (3558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (3558)Termination reason: Refutation
% 1.57/0.61  
% 1.57/0.61  % (3558)Memory used [KB]: 2686
% 1.57/0.61  % (3558)Time elapsed: 0.179 s
% 1.57/0.61  % (3558)------------------------------
% 1.57/0.61  % (3558)------------------------------
% 1.57/0.61  % (3548)Success in time 0.251 s
%------------------------------------------------------------------------------
