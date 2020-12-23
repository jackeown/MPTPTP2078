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
% DateTime   : Thu Dec  3 12:54:34 EST 2020

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 437 expanded)
%              Number of leaves         :   30 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  279 (1161 expanded)
%              Number of equality atoms :   92 ( 288 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2395,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f109,f856,f2362,f149])).

fof(f149,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(sK0,X4)
      | ~ r1_tarski(X4,X3)
      | ~ r1_tarski(X3,k10_relat_1(sK2,sK1)) ) ),
    inference(resolution,[],[f141,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,k10_relat_1(sK2,sK1)) ) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
    & r1_tarski(k9_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f56])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
        & r1_tarski(k9_relat_1(X2,X0),X1)
        & r1_tarski(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
      & r1_tarski(k9_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f2362,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f417,f1746])).

fof(f1746,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f1745,f1718])).

fof(f1718,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f1713,f60])).

fof(f60,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f1713,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f1677,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1677,plain,(
    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
    inference(superposition,[],[f1674,f236])).

fof(f236,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f189,f66])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f189,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK2)) = k10_relat_1(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f72,f60])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1674,plain,(
    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) ),
    inference(superposition,[],[f836,f1613])).

fof(f1613,plain,(
    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f1610,f109])).

fof(f1610,plain,(
    ! [X116] :
      ( ~ r1_tarski(k1_relat_1(sK2),X116)
      | k2_xboole_0(sK0,X116) = X116 ) ),
    inference(resolution,[],[f441,f62])).

fof(f62,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f441,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,X8)
      | k2_xboole_0(X6,X7) = X7
      | ~ r1_tarski(X8,X7) ) ),
    inference(subsumption_resolution,[],[f430,f109])).

fof(f430,plain,(
    ! [X6,X8,X7] :
      ( k2_xboole_0(X6,X7) = X7
      | ~ r1_tarski(X7,X7)
      | ~ r1_tarski(X6,X8)
      | ~ r1_tarski(X8,X7) ) ),
    inference(resolution,[],[f130,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X2,X1),X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f93,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f130,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X4),X5)
      | k2_xboole_0(X3,X4) = X5
      | ~ r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f87,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f836,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f572,f826])).

fof(f826,plain,(
    ! [X48,X49] : k2_xboole_0(X48,k10_relat_1(k6_relat_1(X48),X49)) = X48 ),
    inference(resolution,[],[f270,f112])).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f80,f68])).

fof(f68,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f270,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f265,f109])).

fof(f265,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X2
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,X2) ) ),
    inference(resolution,[],[f129,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f87,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f572,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f208,f119])).

fof(f119,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f118,f68])).

fof(f118,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f116,f69])).

fof(f69,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f116,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f70,f66])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f208,plain,(
    ! [X4,X2,X3] : k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f90,f66])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f1745,plain,(
    k1_relat_1(k7_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f504,f1743])).

fof(f1743,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f1739,f60])).

fof(f1739,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f202,f1718])).

fof(f202,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f201,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f201,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f199,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f199,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f73,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f504,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0))) ),
    inference(resolution,[],[f117,f60])).

fof(f117,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f70,f79])).

fof(f417,plain,(
    ! [X4,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK2,X4),X5),k10_relat_1(sK2,X5)) ),
    inference(superposition,[],[f226,f216])).

fof(f216,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f108,f60])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f89,f105])).

fof(f105,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f77,f104])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f88,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f96,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f97,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f98,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f88,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f78,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f226,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f106,f107])).

fof(f107,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f76,f105,f105])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f75,f105])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f856,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f732,f819])).

fof(f819,plain,(
    sK1 = k2_xboole_0(sK1,k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f270,f63])).

fof(f63,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f732,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0))) ),
    inference(resolution,[],[f250,f109])).

fof(f250,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,k10_relat_1(sK2,X5))
      | r1_tarski(X6,k10_relat_1(sK2,k2_xboole_0(X4,X5))) ) ),
    inference(superposition,[],[f92,f207])).

fof(f207,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f90,f60])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:53:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (818610176)
% 0.20/0.37  ipcrm: permission denied for id (818675715)
% 0.20/0.37  ipcrm: permission denied for id (818708484)
% 0.20/0.37  ipcrm: permission denied for id (818741253)
% 0.20/0.38  ipcrm: permission denied for id (818937868)
% 0.20/0.38  ipcrm: permission denied for id (818970637)
% 0.20/0.39  ipcrm: permission denied for id (819134482)
% 0.20/0.39  ipcrm: permission denied for id (819232789)
% 0.20/0.40  ipcrm: permission denied for id (819363865)
% 0.20/0.40  ipcrm: permission denied for id (819429403)
% 0.20/0.40  ipcrm: permission denied for id (819462172)
% 0.20/0.40  ipcrm: permission denied for id (819527710)
% 0.20/0.41  ipcrm: permission denied for id (819658786)
% 0.20/0.41  ipcrm: permission denied for id (819691555)
% 0.20/0.41  ipcrm: permission denied for id (819724324)
% 0.20/0.42  ipcrm: permission denied for id (819822631)
% 0.20/0.42  ipcrm: permission denied for id (819855400)
% 0.20/0.42  ipcrm: permission denied for id (819920938)
% 0.20/0.42  ipcrm: permission denied for id (819953707)
% 0.20/0.42  ipcrm: permission denied for id (819986476)
% 0.20/0.42  ipcrm: permission denied for id (820019245)
% 0.20/0.42  ipcrm: permission denied for id (820052014)
% 0.20/0.43  ipcrm: permission denied for id (820084783)
% 0.20/0.43  ipcrm: permission denied for id (820117552)
% 0.21/0.43  ipcrm: permission denied for id (820314166)
% 0.21/0.44  ipcrm: permission denied for id (820510779)
% 0.21/0.44  ipcrm: permission denied for id (820543549)
% 0.21/0.45  ipcrm: permission denied for id (820609088)
% 0.21/0.45  ipcrm: permission denied for id (820641857)
% 0.21/0.46  ipcrm: permission denied for id (820838472)
% 0.21/0.46  ipcrm: permission denied for id (820904011)
% 0.21/0.47  ipcrm: permission denied for id (821035088)
% 0.21/0.48  ipcrm: permission denied for id (821264471)
% 0.21/0.48  ipcrm: permission denied for id (821297240)
% 0.21/0.48  ipcrm: permission denied for id (821330009)
% 0.21/0.48  ipcrm: permission denied for id (821362778)
% 0.21/0.49  ipcrm: permission denied for id (821526623)
% 0.21/0.49  ipcrm: permission denied for id (821592161)
% 0.21/0.49  ipcrm: permission denied for id (821690468)
% 0.21/0.49  ipcrm: permission denied for id (821756006)
% 0.21/0.50  ipcrm: permission denied for id (821821544)
% 0.21/0.50  ipcrm: permission denied for id (821887082)
% 0.21/0.50  ipcrm: permission denied for id (821952620)
% 0.21/0.51  ipcrm: permission denied for id (822083696)
% 0.21/0.51  ipcrm: permission denied for id (822116465)
% 0.21/0.51  ipcrm: permission denied for id (822149234)
% 0.21/0.51  ipcrm: permission denied for id (822182003)
% 0.21/0.51  ipcrm: permission denied for id (822214772)
% 0.21/0.52  ipcrm: permission denied for id (822444154)
% 0.21/0.52  ipcrm: permission denied for id (822476923)
% 0.21/0.52  ipcrm: permission denied for id (822509692)
% 0.21/0.52  ipcrm: permission denied for id (822575230)
% 0.88/0.65  % (18852)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.88/0.66  % (18844)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.88/0.68  % (18835)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.69  % (18833)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.69  % (18855)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.69  % (18832)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.34/0.70  % (18834)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.70  % (18842)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.70  % (18847)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.72  % (18831)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.73  % (18854)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.73  % (18857)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.73  % (18830)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.73  % (18859)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.74  % (18851)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.74  % (18841)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.74  % (18845)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.74  % (18846)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.75  % (18836)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.75  % (18837)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.75  % (18850)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.75  % (18839)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.90/0.76  % (18840)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.90/0.76  % (18838)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.90/0.77  % (18853)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.03/0.78  % (18848)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.03/0.78  % (18849)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.03/0.79  % (18858)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.03/0.81  % (18856)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.03/0.81  % (18843)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 3.19/0.94  % (18852)Refutation found. Thanks to Tanya!
% 3.19/0.94  % SZS status Theorem for theBenchmark
% 3.19/0.95  % SZS output start Proof for theBenchmark
% 3.19/0.95  fof(f2395,plain,(
% 3.19/0.95    $false),
% 3.19/0.95    inference(unit_resulting_resolution,[],[f109,f856,f2362,f149])).
% 3.19/0.95  fof(f149,plain,(
% 3.19/0.95    ( ! [X4,X3] : (~r1_tarski(sK0,X4) | ~r1_tarski(X4,X3) | ~r1_tarski(X3,k10_relat_1(sK2,sK1))) )),
% 3.19/0.95    inference(resolution,[],[f141,f94])).
% 3.19/0.95  fof(f94,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f53])).
% 3.19/0.95  fof(f53,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.19/0.95    inference(flattening,[],[f52])).
% 3.19/0.95  fof(f52,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.19/0.95    inference(ennf_transformation,[],[f6])).
% 3.19/0.95  fof(f6,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.19/0.95  fof(f141,plain,(
% 3.19/0.95    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,k10_relat_1(sK2,sK1))) )),
% 3.19/0.95    inference(resolution,[],[f94,f64])).
% 3.19/0.95  fof(f64,plain,(
% 3.19/0.95    ~r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 3.19/0.95    inference(cnf_transformation,[],[f57])).
% 3.19/0.95  fof(f57,plain,(
% 3.19/0.95    ~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.19/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f56])).
% 3.19/0.95  fof(f56,plain,(
% 3.19/0.95    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.19/0.95    introduced(choice_axiom,[])).
% 3.19/0.95  fof(f35,plain,(
% 3.19/0.95    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.19/0.95    inference(flattening,[],[f34])).
% 3.19/0.95  fof(f34,plain,(
% 3.19/0.95    ? [X0,X1,X2] : ((~r1_tarski(X0,k10_relat_1(X2,X1)) & (r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.19/0.95    inference(ennf_transformation,[],[f33])).
% 3.19/0.95  fof(f33,negated_conjecture,(
% 3.19/0.95    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.19/0.95    inference(negated_conjecture,[],[f32])).
% 3.19/0.95  fof(f32,conjecture,(
% 3.19/0.95    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 3.19/0.95  fof(f2362,plain,(
% 3.19/0.95    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 3.19/0.95    inference(superposition,[],[f417,f1746])).
% 3.19/0.95  fof(f1746,plain,(
% 3.19/0.95    sK0 = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0))),
% 3.19/0.95    inference(forward_demodulation,[],[f1745,f1718])).
% 3.19/0.95  fof(f1718,plain,(
% 3.19/0.95    sK0 = k1_relat_1(k7_relat_1(sK2,sK0))),
% 3.19/0.95    inference(subsumption_resolution,[],[f1713,f60])).
% 3.19/0.95  fof(f60,plain,(
% 3.19/0.95    v1_relat_1(sK2)),
% 3.19/0.95    inference(cnf_transformation,[],[f57])).
% 3.19/0.95  fof(f1713,plain,(
% 3.19/0.95    sK0 = k1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 3.19/0.95    inference(superposition,[],[f1677,f82])).
% 3.19/0.95  fof(f82,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f43])).
% 3.19/0.95  fof(f43,plain,(
% 3.19/0.95    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.19/0.95    inference(ennf_transformation,[],[f29])).
% 3.19/0.95  fof(f29,axiom,(
% 3.19/0.95    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 3.19/0.95  fof(f1677,plain,(
% 3.19/0.95    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2))),
% 3.19/0.95    inference(superposition,[],[f1674,f236])).
% 3.19/0.95  fof(f236,plain,(
% 3.19/0.95    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2))) )),
% 3.19/0.95    inference(resolution,[],[f189,f66])).
% 3.19/0.95  fof(f66,plain,(
% 3.19/0.95    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.19/0.95    inference(cnf_transformation,[],[f30])).
% 3.19/0.95  fof(f30,axiom,(
% 3.19/0.95    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.19/0.95  fof(f189,plain,(
% 3.19/0.95    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK2)) = k10_relat_1(X0,k1_relat_1(sK2))) )),
% 3.19/0.95    inference(resolution,[],[f72,f60])).
% 3.19/0.95  fof(f72,plain,(
% 3.19/0.95    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f38])).
% 3.19/0.95  fof(f38,plain,(
% 3.19/0.95    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.19/0.95    inference(ennf_transformation,[],[f26])).
% 3.19/0.95  fof(f26,axiom,(
% 3.19/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 3.19/0.95  fof(f1674,plain,(
% 3.19/0.95    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2))),
% 3.19/0.95    inference(superposition,[],[f836,f1613])).
% 3.19/0.95  fof(f1613,plain,(
% 3.19/0.95    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2))),
% 3.19/0.95    inference(resolution,[],[f1610,f109])).
% 3.19/0.95  fof(f1610,plain,(
% 3.19/0.95    ( ! [X116] : (~r1_tarski(k1_relat_1(sK2),X116) | k2_xboole_0(sK0,X116) = X116) )),
% 3.19/0.95    inference(resolution,[],[f441,f62])).
% 3.19/0.95  fof(f62,plain,(
% 3.19/0.95    r1_tarski(sK0,k1_relat_1(sK2))),
% 3.19/0.95    inference(cnf_transformation,[],[f57])).
% 3.19/0.95  fof(f441,plain,(
% 3.19/0.95    ( ! [X6,X8,X7] : (~r1_tarski(X6,X8) | k2_xboole_0(X6,X7) = X7 | ~r1_tarski(X8,X7)) )),
% 3.19/0.95    inference(subsumption_resolution,[],[f430,f109])).
% 3.19/0.95  fof(f430,plain,(
% 3.19/0.95    ( ! [X6,X8,X7] : (k2_xboole_0(X6,X7) = X7 | ~r1_tarski(X7,X7) | ~r1_tarski(X6,X8) | ~r1_tarski(X8,X7)) )),
% 3.19/0.95    inference(resolution,[],[f130,f163])).
% 3.19/0.95  fof(f163,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X2,X1),X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.19/0.95    inference(superposition,[],[f93,f84])).
% 3.19/0.95  fof(f84,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f45])).
% 3.19/0.95  fof(f45,plain,(
% 3.19/0.95    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.19/0.95    inference(ennf_transformation,[],[f4])).
% 3.19/0.95  fof(f4,axiom,(
% 3.19/0.95    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.19/0.95  fof(f93,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f51])).
% 3.19/0.95  fof(f51,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 3.19/0.95    inference(ennf_transformation,[],[f10])).
% 3.19/0.95  fof(f10,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 3.19/0.95  fof(f130,plain,(
% 3.19/0.95    ( ! [X4,X5,X3] : (~r1_tarski(k2_xboole_0(X3,X4),X5) | k2_xboole_0(X3,X4) = X5 | ~r1_tarski(X5,X4)) )),
% 3.19/0.95    inference(resolution,[],[f87,f92])).
% 3.19/0.95  fof(f92,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f50])).
% 3.19/0.95  fof(f50,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.19/0.95    inference(ennf_transformation,[],[f3])).
% 3.19/0.95  fof(f3,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.19/0.95  fof(f87,plain,(
% 3.19/0.95    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f59])).
% 3.19/0.95  fof(f59,plain,(
% 3.19/0.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.19/0.95    inference(flattening,[],[f58])).
% 3.19/0.95  fof(f58,plain,(
% 3.19/0.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.19/0.95    inference(nnf_transformation,[],[f2])).
% 3.19/0.95  fof(f2,axiom,(
% 3.19/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.19/0.95  fof(f836,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = X0) )),
% 3.19/0.95    inference(backward_demodulation,[],[f572,f826])).
% 3.19/0.95  fof(f826,plain,(
% 3.19/0.95    ( ! [X48,X49] : (k2_xboole_0(X48,k10_relat_1(k6_relat_1(X48),X49)) = X48) )),
% 3.19/0.95    inference(resolution,[],[f270,f112])).
% 3.19/0.95  fof(f112,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.19/0.95    inference(subsumption_resolution,[],[f111,f66])).
% 3.19/0.95  fof(f111,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.19/0.95    inference(superposition,[],[f80,f68])).
% 3.19/0.95  fof(f68,plain,(
% 3.19/0.95    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.19/0.95    inference(cnf_transformation,[],[f27])).
% 3.19/0.95  fof(f27,axiom,(
% 3.19/0.95    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.19/0.95  fof(f80,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f41])).
% 3.19/0.95  fof(f41,plain,(
% 3.19/0.95    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.19/0.95    inference(ennf_transformation,[],[f21])).
% 3.19/0.95  fof(f21,axiom,(
% 3.19/0.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 3.19/0.95  fof(f270,plain,(
% 3.19/0.95    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k2_xboole_0(X2,X3) = X2) )),
% 3.19/0.95    inference(subsumption_resolution,[],[f265,f109])).
% 3.19/0.95  fof(f265,plain,(
% 3.19/0.95    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X2 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,X2)) )),
% 3.19/0.95    inference(resolution,[],[f129,f95])).
% 3.19/0.95  fof(f95,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f55])).
% 3.19/0.95  fof(f55,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.19/0.95    inference(flattening,[],[f54])).
% 3.19/0.95  fof(f54,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.19/0.95    inference(ennf_transformation,[],[f9])).
% 3.19/0.95  fof(f9,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.19/0.95  fof(f129,plain,(
% 3.19/0.95    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 3.19/0.95    inference(resolution,[],[f87,f74])).
% 3.19/0.95  fof(f74,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.19/0.95    inference(cnf_transformation,[],[f8])).
% 3.19/0.95  fof(f8,axiom,(
% 3.19/0.95    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.19/0.95  fof(f572,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 3.19/0.95    inference(superposition,[],[f208,f119])).
% 3.19/0.95  fof(f119,plain,(
% 3.19/0.95    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 3.19/0.95    inference(forward_demodulation,[],[f118,f68])).
% 3.19/0.95  fof(f118,plain,(
% 3.19/0.95    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 3.19/0.95    inference(forward_demodulation,[],[f116,f69])).
% 3.19/0.95  fof(f69,plain,(
% 3.19/0.95    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.19/0.95    inference(cnf_transformation,[],[f27])).
% 3.19/0.95  fof(f116,plain,(
% 3.19/0.95    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 3.19/0.95    inference(resolution,[],[f70,f66])).
% 3.19/0.95  fof(f70,plain,(
% 3.19/0.95    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 3.19/0.95    inference(cnf_transformation,[],[f36])).
% 3.19/0.95  fof(f36,plain,(
% 3.19/0.95    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.19/0.95    inference(ennf_transformation,[],[f22])).
% 3.19/0.95  fof(f22,axiom,(
% 3.19/0.95    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 3.19/0.95  fof(f208,plain,(
% 3.19/0.95    ( ! [X4,X2,X3] : (k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4))) )),
% 3.19/0.95    inference(resolution,[],[f90,f66])).
% 3.19/0.95  fof(f90,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 3.19/0.95    inference(cnf_transformation,[],[f47])).
% 3.19/0.95  fof(f47,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.19/0.95    inference(ennf_transformation,[],[f24])).
% 3.19/0.95  fof(f24,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 3.19/0.95  fof(f1745,plain,(
% 3.19/0.95    k1_relat_1(k7_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0))),
% 3.19/0.95    inference(superposition,[],[f504,f1743])).
% 3.19/0.95  fof(f1743,plain,(
% 3.19/0.95    k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK2,sK0))),
% 3.19/0.95    inference(subsumption_resolution,[],[f1739,f60])).
% 3.19/0.95  fof(f1739,plain,(
% 3.19/0.95    k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 3.19/0.95    inference(superposition,[],[f202,f1718])).
% 3.19/0.95  fof(f202,plain,(
% 3.19/0.95    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(X3)) )),
% 3.19/0.95    inference(subsumption_resolution,[],[f201,f79])).
% 3.19/0.95  fof(f79,plain,(
% 3.19/0.95    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f40])).
% 3.19/0.95  fof(f40,plain,(
% 3.19/0.95    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.19/0.95    inference(ennf_transformation,[],[f18])).
% 3.19/0.95  fof(f18,axiom,(
% 3.19/0.95    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.19/0.95  fof(f201,plain,(
% 3.19/0.95    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 3.19/0.95    inference(subsumption_resolution,[],[f199,f81])).
% 3.19/0.95  fof(f81,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f42])).
% 3.19/0.95  fof(f42,plain,(
% 3.19/0.95    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.19/0.95    inference(ennf_transformation,[],[f28])).
% 3.19/0.95  fof(f28,axiom,(
% 3.19/0.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 3.19/0.95  fof(f199,plain,(
% 3.19/0.95    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 3.19/0.95    inference(superposition,[],[f73,f71])).
% 3.19/0.95  fof(f71,plain,(
% 3.19/0.95    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f37])).
% 3.19/0.95  fof(f37,plain,(
% 3.19/0.95    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.19/0.95    inference(ennf_transformation,[],[f19])).
% 3.19/0.95  fof(f19,axiom,(
% 3.19/0.95    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 3.19/0.95  fof(f73,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f39])).
% 3.19/0.95  fof(f39,plain,(
% 3.19/0.95    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 3.19/0.95    inference(ennf_transformation,[],[f20])).
% 3.19/0.95  fof(f20,axiom,(
% 3.19/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 3.19/0.95  fof(f504,plain,(
% 3.19/0.95    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0)))) )),
% 3.19/0.95    inference(resolution,[],[f117,f60])).
% 3.19/0.95  fof(f117,plain,(
% 3.19/0.95    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))) )),
% 3.19/0.95    inference(resolution,[],[f70,f79])).
% 3.19/0.95  fof(f417,plain,(
% 3.19/0.95    ( ! [X4,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK2,X4),X5),k10_relat_1(sK2,X5))) )),
% 3.19/0.95    inference(superposition,[],[f226,f216])).
% 3.19/0.95  fof(f216,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK2,X1)))) )),
% 3.19/0.95    inference(resolution,[],[f108,f60])).
% 3.19/0.95  fof(f108,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 3.19/0.95    inference(definition_unfolding,[],[f89,f105])).
% 3.19/0.95  fof(f105,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.19/0.95    inference(definition_unfolding,[],[f77,f104])).
% 3.19/0.95  fof(f104,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.19/0.95    inference(definition_unfolding,[],[f78,f103])).
% 3.19/0.95  fof(f103,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.19/0.95    inference(definition_unfolding,[],[f88,f102])).
% 3.19/0.95  fof(f102,plain,(
% 3.19/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.19/0.95    inference(definition_unfolding,[],[f96,f101])).
% 3.19/0.95  fof(f101,plain,(
% 3.19/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.19/0.95    inference(definition_unfolding,[],[f97,f100])).
% 3.19/0.95  fof(f100,plain,(
% 3.19/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.19/0.95    inference(definition_unfolding,[],[f98,f99])).
% 3.19/0.95  fof(f99,plain,(
% 3.19/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f16])).
% 3.19/0.95  fof(f16,axiom,(
% 3.19/0.95    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.19/0.95  fof(f98,plain,(
% 3.19/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f15])).
% 3.19/0.95  fof(f15,axiom,(
% 3.19/0.95    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.19/0.95  fof(f97,plain,(
% 3.19/0.95    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f14])).
% 3.19/0.95  fof(f14,axiom,(
% 3.19/0.95    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.19/0.95  fof(f96,plain,(
% 3.19/0.95    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f13])).
% 3.19/0.95  fof(f13,axiom,(
% 3.19/0.95    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.19/0.95  fof(f88,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f12])).
% 3.19/0.95  fof(f12,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.19/0.95  fof(f78,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f11])).
% 3.19/0.95  fof(f11,axiom,(
% 3.19/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.19/0.95  fof(f77,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.19/0.95    inference(cnf_transformation,[],[f17])).
% 3.19/0.95  fof(f17,axiom,(
% 3.19/0.95    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.19/0.95  fof(f89,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f46])).
% 3.19/0.95  fof(f46,plain,(
% 3.19/0.95    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.19/0.95    inference(ennf_transformation,[],[f31])).
% 3.19/0.95  fof(f31,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 3.19/0.95  fof(f226,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0)) )),
% 3.19/0.95    inference(superposition,[],[f106,f107])).
% 3.19/0.95  fof(f107,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 3.19/0.95    inference(definition_unfolding,[],[f76,f105,f105])).
% 3.19/0.95  fof(f76,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f1])).
% 3.19/0.95  fof(f1,axiom,(
% 3.19/0.95    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.19/0.95  fof(f106,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.19/0.95    inference(definition_unfolding,[],[f75,f105])).
% 3.19/0.95  fof(f75,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f5])).
% 3.19/0.95  fof(f5,axiom,(
% 3.19/0.95    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.19/0.95  fof(f856,plain,(
% 3.19/0.95    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))),
% 3.19/0.95    inference(superposition,[],[f732,f819])).
% 3.19/0.95  fof(f819,plain,(
% 3.19/0.95    sK1 = k2_xboole_0(sK1,k9_relat_1(sK2,sK0))),
% 3.19/0.95    inference(resolution,[],[f270,f63])).
% 3.19/0.95  fof(f63,plain,(
% 3.19/0.95    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 3.19/0.95    inference(cnf_transformation,[],[f57])).
% 3.19/0.95  fof(f732,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0)))) )),
% 3.19/0.95    inference(resolution,[],[f250,f109])).
% 3.19/0.95  fof(f250,plain,(
% 3.19/0.95    ( ! [X6,X4,X5] : (~r1_tarski(X6,k10_relat_1(sK2,X5)) | r1_tarski(X6,k10_relat_1(sK2,k2_xboole_0(X4,X5)))) )),
% 3.19/0.95    inference(superposition,[],[f92,f207])).
% 3.19/0.95  fof(f207,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 3.19/0.95    inference(resolution,[],[f90,f60])).
% 3.19/0.95  fof(f109,plain,(
% 3.19/0.95    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.19/0.95    inference(equality_resolution,[],[f86])).
% 3.19/0.95  fof(f86,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.19/0.95    inference(cnf_transformation,[],[f59])).
% 3.19/0.95  % SZS output end Proof for theBenchmark
% 3.19/0.95  % (18852)------------------------------
% 3.19/0.95  % (18852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.95  % (18852)Termination reason: Refutation
% 3.19/0.95  
% 3.19/0.95  % (18852)Memory used [KB]: 9338
% 3.19/0.95  % (18852)Time elapsed: 0.298 s
% 3.19/0.95  % (18852)------------------------------
% 3.19/0.95  % (18852)------------------------------
% 3.19/0.96  % (18692)Success in time 0.591 s
%------------------------------------------------------------------------------
