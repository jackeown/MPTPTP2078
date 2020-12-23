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
% DateTime   : Thu Dec  3 12:54:17 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 271 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   18
%              Number of atoms          :  254 ( 984 expanded)
%              Number of equality atoms :   55 ( 103 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1045,plain,(
    $false ),
    inference(resolution,[],[f1030,f42])).

fof(f42,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f1030,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f1014,f230])).

fof(f230,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1) ),
    inference(resolution,[],[f128,f93])).

fof(f93,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ) ),
    inference(resolution,[],[f79,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f128,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1) ) ),
    inference(resolution,[],[f124,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f124,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f73,f37])).

fof(f73,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(sK2,sK0)),k10_relat_1(X1,k9_relat_1(sK2,sK1))) ) ),
    inference(resolution,[],[f58,f39])).

fof(f39,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f1014,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(forward_demodulation,[],[f1010,f69])).

fof(f69,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f68,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f66,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f51,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f1010,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(sK0),sK0),X1)
      | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1) ) ),
    inference(superposition,[],[f376,f994])).

fof(f994,plain,(
    sK0 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f989,f393])).

fof(f393,plain,(
    ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) ),
    inference(backward_demodulation,[],[f183,f359])).

fof(f359,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f152,f44])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(k6_relat_1(X1))
      | k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f91,f43])).

fof(f43,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f91,plain,(
    ! [X2,X1] :
      ( k10_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k2_funct_1(k6_relat_1(X1)),X2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f183,plain,(
    ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f106,f37])).

fof(f106,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k10_relat_1(k6_relat_1(X3),k10_relat_1(X2,X4)) ) ),
    inference(resolution,[],[f53,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f989,plain,(
    sK0 = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f986,f666])).

fof(f666,plain,(
    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
    inference(resolution,[],[f648,f40])).

fof(f40,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f648,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = X0 ) ),
    inference(resolution,[],[f223,f37])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0 ) ),
    inference(resolution,[],[f134,f44])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0 ) ),
    inference(forward_demodulation,[],[f132,f48])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k6_relat_1(X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f49])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f986,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f902,f983])).

fof(f983,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
    inference(forward_demodulation,[],[f981,f69])).

fof(f981,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k9_relat_1(sK2,k9_relat_1(k6_relat_1(sK0),sK0)) ),
    inference(superposition,[],[f978,f199])).

fof(f199,plain,(
    ! [X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k9_relat_1(sK2,k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f121,f37])).

fof(f121,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f54,f44])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f978,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k9_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),sK0) ),
    inference(superposition,[],[f923,f666])).

fof(f923,plain,(
    ! [X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2))) ),
    inference(resolution,[],[f253,f37])).

fof(f253,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(k6_relat_1(X2),X1)) = k9_relat_1(k5_relat_1(k6_relat_1(X2),X1),k1_relat_1(k5_relat_1(k6_relat_1(X2),X1))) ) ),
    inference(resolution,[],[f67,f44])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(k5_relat_1(X1,X2),k1_relat_1(k5_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f51,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f902,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2))) ),
    inference(resolution,[],[f236,f37])).

fof(f236,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X2),X1),k2_relat_1(k5_relat_1(k6_relat_1(X2),X1))) ) ),
    inference(resolution,[],[f62,f44])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(X1,X2),k2_relat_1(k5_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f50,f57])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f376,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X8),k9_relat_1(k6_relat_1(X8),X6)),X7)
      | ~ r1_tarski(X6,X7) ) ),
    inference(backward_demodulation,[],[f333,f359])).

fof(f333,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k10_relat_1(k6_relat_1(X8),k9_relat_1(k6_relat_1(X8),X6)),X7) ) ),
    inference(resolution,[],[f330,f59])).

fof(f330,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(resolution,[],[f144,f44])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) ) ),
    inference(resolution,[],[f80,f45])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(k6_relat_1(X1))
      | r1_tarski(k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2)),X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f55,f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (15890)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.44  % (15874)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.45  % (15882)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.48  % (15873)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.49  % (15872)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.49  % (15871)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.49  % (15870)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.50  % (15880)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.50  % (15889)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.50  % (15891)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.50  % (15875)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.50  % (15881)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.50  % (15886)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.50  % (15884)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.51  % (15877)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.51  % (15892)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.51  % (15888)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.51  % (15879)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.51  % (15883)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.51  % (15876)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.52  % (15878)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.52  % (15887)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.52  % (15869)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.53  % (15885)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.89/0.61  % (15878)Refutation found. Thanks to Tanya!
% 1.89/0.61  % SZS status Theorem for theBenchmark
% 1.89/0.61  % SZS output start Proof for theBenchmark
% 1.89/0.61  fof(f1045,plain,(
% 1.89/0.61    $false),
% 1.89/0.61    inference(resolution,[],[f1030,f42])).
% 1.89/0.61  fof(f42,plain,(
% 1.89/0.61    ~r1_tarski(sK0,sK1)),
% 1.89/0.61    inference(cnf_transformation,[],[f36])).
% 1.89/0.61  fof(f36,plain,(
% 1.89/0.61    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.89/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35])).
% 1.89/0.61  fof(f35,plain,(
% 1.89/0.61    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f18,plain,(
% 1.89/0.61    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.89/0.61    inference(flattening,[],[f17])).
% 1.89/0.61  fof(f17,plain,(
% 1.89/0.61    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.89/0.61    inference(ennf_transformation,[],[f16])).
% 1.89/0.61  fof(f16,negated_conjecture,(
% 1.89/0.61    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.89/0.61    inference(negated_conjecture,[],[f15])).
% 1.89/0.61  fof(f15,conjecture,(
% 1.89/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 1.89/0.61  fof(f1030,plain,(
% 1.89/0.61    r1_tarski(sK0,sK1)),
% 1.89/0.61    inference(resolution,[],[f1014,f230])).
% 1.89/0.61  fof(f230,plain,(
% 1.89/0.61    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1)),
% 1.89/0.61    inference(resolution,[],[f128,f93])).
% 1.89/0.61  fof(f93,plain,(
% 1.89/0.61    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) )),
% 1.89/0.61    inference(resolution,[],[f89,f37])).
% 1.89/0.61  fof(f37,plain,(
% 1.89/0.61    v1_relat_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f36])).
% 1.89/0.61  fof(f89,plain,(
% 1.89/0.61    ( ! [X0] : (~v1_relat_1(sK2) | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) )),
% 1.89/0.61    inference(resolution,[],[f79,f38])).
% 1.89/0.61  fof(f38,plain,(
% 1.89/0.61    v1_funct_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f36])).
% 1.89/0.61  fof(f79,plain,(
% 1.89/0.61    ( ! [X0] : (~v1_funct_1(sK2) | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) | ~v1_relat_1(sK2)) )),
% 1.89/0.61    inference(resolution,[],[f55,f41])).
% 1.89/0.61  fof(f41,plain,(
% 1.89/0.61    v2_funct_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f36])).
% 1.89/0.61  fof(f55,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f26])).
% 1.89/0.61  fof(f26,plain,(
% 1.89/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(flattening,[],[f25])).
% 1.89/0.61  fof(f25,plain,(
% 1.89/0.61    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.89/0.61    inference(ennf_transformation,[],[f12])).
% 1.89/0.61  fof(f12,axiom,(
% 1.89/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.89/0.61  fof(f128,plain,(
% 1.89/0.61    ( ! [X1] : (~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1) | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1)) )),
% 1.89/0.61    inference(resolution,[],[f124,f59])).
% 1.89/0.61  fof(f59,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f34])).
% 1.89/0.61  fof(f34,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.89/0.61    inference(flattening,[],[f33])).
% 1.89/0.61  fof(f33,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.89/0.61    inference(ennf_transformation,[],[f1])).
% 1.89/0.61  fof(f1,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.89/0.61  fof(f124,plain,(
% 1.89/0.61    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 1.89/0.61    inference(resolution,[],[f73,f37])).
% 1.89/0.61  fof(f73,plain,(
% 1.89/0.61    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(sK2,sK0)),k10_relat_1(X1,k9_relat_1(sK2,sK1)))) )),
% 1.89/0.61    inference(resolution,[],[f58,f39])).
% 1.89/0.61  fof(f39,plain,(
% 1.89/0.61    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.89/0.61    inference(cnf_transformation,[],[f36])).
% 1.89/0.61  fof(f58,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f32])).
% 1.89/0.61  fof(f32,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.89/0.61    inference(flattening,[],[f31])).
% 1.89/0.61  fof(f31,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.89/0.61    inference(ennf_transformation,[],[f6])).
% 1.89/0.61  fof(f6,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 1.89/0.61  fof(f1014,plain,(
% 1.89/0.61    ( ! [X1] : (~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1) | r1_tarski(sK0,X1)) )),
% 1.89/0.61    inference(forward_demodulation,[],[f1010,f69])).
% 1.89/0.61  fof(f69,plain,(
% 1.89/0.61    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.89/0.61    inference(forward_demodulation,[],[f68,f49])).
% 1.89/0.61  fof(f49,plain,(
% 1.89/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.89/0.61    inference(cnf_transformation,[],[f9])).
% 1.89/0.61  fof(f9,axiom,(
% 1.89/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.89/0.61  fof(f68,plain,(
% 1.89/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 1.89/0.61    inference(forward_demodulation,[],[f66,f48])).
% 1.89/0.61  fof(f48,plain,(
% 1.89/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.89/0.61    inference(cnf_transformation,[],[f9])).
% 1.89/0.61  fof(f66,plain,(
% 1.89/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 1.89/0.61    inference(resolution,[],[f51,f44])).
% 1.89/0.61  fof(f44,plain,(
% 1.89/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f10])).
% 1.89/0.61  fof(f10,axiom,(
% 1.89/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.89/0.61  fof(f51,plain,(
% 1.89/0.61    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f20])).
% 1.89/0.61  fof(f20,plain,(
% 1.89/0.61    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f3])).
% 1.89/0.61  fof(f3,axiom,(
% 1.89/0.61    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.89/0.61  fof(f1010,plain,(
% 1.89/0.61    ( ! [X1] : (r1_tarski(k9_relat_1(k6_relat_1(sK0),sK0),X1) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X1)) )),
% 1.89/0.61    inference(superposition,[],[f376,f994])).
% 1.89/0.61  fof(f994,plain,(
% 1.89/0.61    sK0 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 1.89/0.61    inference(superposition,[],[f989,f393])).
% 1.89/0.61  fof(f393,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1))) )),
% 1.89/0.61    inference(backward_demodulation,[],[f183,f359])).
% 1.89/0.61  fof(f359,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.89/0.61    inference(resolution,[],[f152,f44])).
% 1.89/0.61  fof(f152,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.89/0.61    inference(resolution,[],[f92,f45])).
% 1.89/0.61  fof(f45,plain,(
% 1.89/0.61    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f10])).
% 1.89/0.61  fof(f92,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~v1_funct_1(k6_relat_1(X1)) | k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.89/0.61    inference(forward_demodulation,[],[f91,f43])).
% 1.89/0.61  fof(f43,plain,(
% 1.89/0.61    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f14])).
% 1.89/0.61  fof(f14,axiom,(
% 1.89/0.61    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 1.89/0.61  fof(f91,plain,(
% 1.89/0.61    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k2_funct_1(k6_relat_1(X1)),X2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.89/0.61    inference(resolution,[],[f56,f47])).
% 1.89/0.61  fof(f47,plain,(
% 1.89/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f11])).
% 1.89/0.61  fof(f11,axiom,(
% 1.89/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.89/0.61  fof(f56,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f28])).
% 1.89/0.61  fof(f28,plain,(
% 1.89/0.61    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(flattening,[],[f27])).
% 1.89/0.61  fof(f27,plain,(
% 1.89/0.61    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.89/0.61    inference(ennf_transformation,[],[f13])).
% 1.89/0.61  fof(f13,axiom,(
% 1.89/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.89/0.61  fof(f183,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1))) )),
% 1.89/0.61    inference(resolution,[],[f106,f37])).
% 1.89/0.61  fof(f106,plain,(
% 1.89/0.61    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k10_relat_1(k6_relat_1(X3),k10_relat_1(X2,X4))) )),
% 1.89/0.61    inference(resolution,[],[f53,f44])).
% 1.89/0.61  fof(f53,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f23])).
% 1.89/0.61  fof(f23,plain,(
% 1.89/0.61    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(ennf_transformation,[],[f7])).
% 1.89/0.61  fof(f7,axiom,(
% 1.89/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 1.89/0.61  fof(f989,plain,(
% 1.89/0.61    sK0 = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0))),
% 1.89/0.61    inference(forward_demodulation,[],[f986,f666])).
% 1.89/0.61  fof(f666,plain,(
% 1.89/0.61    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2))),
% 1.89/0.61    inference(resolution,[],[f648,f40])).
% 1.89/0.61  fof(f40,plain,(
% 1.89/0.61    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.89/0.61    inference(cnf_transformation,[],[f36])).
% 1.89/0.61  fof(f648,plain,(
% 1.89/0.61    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = X0) )),
% 1.89/0.61    inference(resolution,[],[f223,f37])).
% 1.89/0.61  fof(f223,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0) )),
% 1.89/0.61    inference(resolution,[],[f134,f44])).
% 1.89/0.61  fof(f134,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0) )),
% 1.89/0.61    inference(forward_demodulation,[],[f132,f48])).
% 1.89/0.61  fof(f132,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k6_relat_1(X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.89/0.61    inference(superposition,[],[f52,f49])).
% 1.89/0.61  fof(f52,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f22])).
% 1.89/0.61  fof(f22,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.89/0.61    inference(flattening,[],[f21])).
% 1.89/0.61  fof(f21,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f8])).
% 1.89/0.61  fof(f8,axiom,(
% 1.89/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.89/0.61  fof(f986,plain,(
% 1.89/0.61    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0))),
% 1.89/0.61    inference(superposition,[],[f902,f983])).
% 1.89/0.61  fof(f983,plain,(
% 1.89/0.61    k9_relat_1(sK2,sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2))),
% 1.89/0.61    inference(forward_demodulation,[],[f981,f69])).
% 1.89/0.61  fof(f981,plain,(
% 1.89/0.61    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k9_relat_1(sK2,k9_relat_1(k6_relat_1(sK0),sK0))),
% 1.89/0.61    inference(superposition,[],[f978,f199])).
% 1.89/0.61  fof(f199,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k9_relat_1(sK2,k9_relat_1(k6_relat_1(X0),X1))) )),
% 1.89/0.61    inference(resolution,[],[f121,f37])).
% 1.89/0.61  fof(f121,plain,(
% 1.89/0.61    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4))) )),
% 1.89/0.61    inference(resolution,[],[f54,f44])).
% 1.89/0.61  fof(f54,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f24])).
% 1.89/0.61  fof(f24,plain,(
% 1.89/0.61    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(ennf_transformation,[],[f4])).
% 1.89/0.61  fof(f4,axiom,(
% 1.89/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 1.89/0.61  fof(f978,plain,(
% 1.89/0.61    k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k9_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),sK0)),
% 1.89/0.61    inference(superposition,[],[f923,f666])).
% 1.89/0.61  fof(f923,plain,(
% 1.89/0.61    ( ! [X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)))) )),
% 1.89/0.61    inference(resolution,[],[f253,f37])).
% 1.89/0.61  fof(f253,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(k6_relat_1(X2),X1)) = k9_relat_1(k5_relat_1(k6_relat_1(X2),X1),k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)))) )),
% 1.89/0.61    inference(resolution,[],[f67,f44])).
% 1.89/0.61  fof(f67,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(k5_relat_1(X1,X2),k1_relat_1(k5_relat_1(X1,X2)))) )),
% 1.89/0.61    inference(resolution,[],[f51,f57])).
% 1.89/0.61  fof(f57,plain,(
% 1.89/0.61    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f30])).
% 1.89/0.61  fof(f30,plain,(
% 1.89/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.89/0.61    inference(flattening,[],[f29])).
% 1.89/0.61  fof(f29,plain,(
% 1.89/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f2])).
% 1.89/0.61  fof(f2,axiom,(
% 1.89/0.61    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.89/0.61  fof(f902,plain,(
% 1.89/0.61    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2)))) )),
% 1.89/0.61    inference(resolution,[],[f236,f37])).
% 1.89/0.61  fof(f236,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X2),X1),k2_relat_1(k5_relat_1(k6_relat_1(X2),X1)))) )),
% 1.89/0.61    inference(resolution,[],[f62,f44])).
% 1.89/0.61  fof(f62,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(X1,X2),k2_relat_1(k5_relat_1(X1,X2)))) )),
% 1.89/0.61    inference(resolution,[],[f50,f57])).
% 1.89/0.61  fof(f50,plain,(
% 1.89/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f19])).
% 1.89/0.61  fof(f19,plain,(
% 1.89/0.61    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f5])).
% 1.89/0.61  fof(f5,axiom,(
% 1.89/0.61    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.89/0.61  fof(f376,plain,(
% 1.89/0.61    ( ! [X6,X8,X7] : (r1_tarski(k9_relat_1(k6_relat_1(X8),k9_relat_1(k6_relat_1(X8),X6)),X7) | ~r1_tarski(X6,X7)) )),
% 1.89/0.61    inference(backward_demodulation,[],[f333,f359])).
% 1.89/0.61  fof(f333,plain,(
% 1.89/0.61    ( ! [X6,X8,X7] : (~r1_tarski(X6,X7) | r1_tarski(k10_relat_1(k6_relat_1(X8),k9_relat_1(k6_relat_1(X8),X6)),X7)) )),
% 1.89/0.61    inference(resolution,[],[f330,f59])).
% 1.89/0.61  fof(f330,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 1.89/0.61    inference(resolution,[],[f144,f44])).
% 1.89/0.61  fof(f144,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | r1_tarski(k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 1.89/0.61    inference(resolution,[],[f80,f45])).
% 1.89/0.61  fof(f80,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~v1_funct_1(k6_relat_1(X1)) | r1_tarski(k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2)),X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.89/0.61    inference(resolution,[],[f55,f47])).
% 1.89/0.61  % SZS output end Proof for theBenchmark
% 1.89/0.61  % (15878)------------------------------
% 1.89/0.61  % (15878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (15878)Termination reason: Refutation
% 1.89/0.61  
% 1.89/0.61  % (15878)Memory used [KB]: 2558
% 1.89/0.61  % (15878)Time elapsed: 0.209 s
% 1.89/0.61  % (15878)------------------------------
% 1.89/0.61  % (15878)------------------------------
% 1.89/0.61  % (15868)Success in time 0.265 s
%------------------------------------------------------------------------------
