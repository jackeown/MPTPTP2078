%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:37 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 785 expanded)
%              Number of leaves         :   17 ( 196 expanded)
%              Depth                    :   22
%              Number of atoms          :  275 (3010 expanded)
%              Number of equality atoms :   82 ( 731 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2199,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2188,f141])).

fof(f141,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f139,f57])).

fof(f57,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f48])).

fof(f48,plain,
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

fof(f28,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f139,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f105,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f105,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f101,f53])).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f55,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f55,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f2188,plain,(
    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f665,f1855])).

fof(f1855,plain,(
    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1854,f87])).

fof(f87,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f1854,plain,(
    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f1838,f855])).

fof(f855,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f438,f852])).

fof(f852,plain,(
    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f845,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f845,plain,(
    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f835,f87])).

fof(f835,plain,(
    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(superposition,[],[f401,f190])).

fof(f190,plain,(
    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(superposition,[],[f108,f145])).

fof(f145,plain,(
    k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f142,f86])).

fof(f86,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(resolution,[],[f53,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f142,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(superposition,[],[f95,f87])).

fof(f95,plain,(
    ! [X3] : k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k3_xboole_0(X3,k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f94,f86])).

fof(f94,plain,(
    ! [X3] : k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k3_xboole_0(X3,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f90,f53])).

fof(f90,plain,(
    ! [X3] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k3_xboole_0(X3,k9_relat_1(sK1,k1_relat_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,k2_relat_1(sK1)),X3) ),
    inference(resolution,[],[f96,f59])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k2_relat_1(sK1)),X0) ),
    inference(backward_demodulation,[],[f91,f95])).

fof(f91,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f88,f53])).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f54,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f401,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK1,k4_xboole_0(X0,X1)),k10_relat_1(sK1,X0)) ),
    inference(superposition,[],[f79,f164])).

fof(f164,plain,(
    ! [X2,X3] : k4_xboole_0(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) = k10_relat_1(sK1,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f93,f82])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f93,plain,(
    ! [X2,X1] : k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2)) = k10_relat_1(sK1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f92,f82])).

fof(f92,plain,(
    ! [X2,X1] : k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2)) ),
    inference(subsumption_resolution,[],[f89,f53])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f54,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f438,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f167,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f167,plain,(
    ! [X0] : k10_relat_1(sK1,k4_xboole_0(X0,k2_relat_1(sK1))) = k4_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f163,f82])).

fof(f163,plain,(
    ! [X0] : k10_relat_1(sK1,k4_xboole_0(X0,k2_relat_1(sK1))) = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f93,f87])).

fof(f1838,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(superposition,[],[f403,f534])).

fof(f534,plain,(
    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f514,f526])).

fof(f526,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f525,f430])).

fof(f430,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_relat_1(sK1),X4),k2_relat_1(sK1)) ),
    inference(resolution,[],[f375,f59])).

fof(f375,plain,(
    ! [X5] : r1_tarski(k3_xboole_0(k2_relat_1(sK1),X5),k2_relat_1(sK1)) ),
    inference(superposition,[],[f242,f145])).

fof(f242,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,k2_relat_1(sK1)),X2),X1) ),
    inference(superposition,[],[f202,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f202,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(k3_xboole_0(X4,k2_relat_1(sK1)),X5),X4) ),
    inference(resolution,[],[f106,f79])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,k2_relat_1(sK1)))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f96,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f525,plain,(
    k9_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k2_relat_1(sK1))),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f510,f492])).

fof(f492,plain,(
    ! [X0] : k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f491,f65])).

fof(f491,plain,(
    ! [X0] : k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f481,f176])).

fof(f176,plain,(
    ! [X0] : k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f170,f82])).

fof(f170,plain,(
    ! [X0] : k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X0)) ),
    inference(superposition,[],[f100,f86])).

fof(f100,plain,(
    ! [X0,X1] : k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f99,f82])).

fof(f99,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f98,f53])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f97,f54])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f56,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f56,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f481,plain,(
    ! [X0] : k4_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0))) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(superposition,[],[f176,f65])).

fof(f510,plain,(
    k9_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),k2_relat_1(sK1)) ),
    inference(superposition,[],[f177,f108])).

fof(f177,plain,(
    ! [X0] : k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k4_xboole_0(k9_relat_1(sK1,X0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f172,f82])).

fof(f172,plain,(
    ! [X0] : k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k6_subset_1(k9_relat_1(sK1,X0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f100,f86])).

fof(f514,plain,(
    k9_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f177,f104])).

fof(f104,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f55,f59])).

fof(f403,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k10_relat_1(sK1,k4_xboole_0(X4,X5))
      | r1_tarski(k10_relat_1(sK1,X4),k10_relat_1(sK1,X5)) ) ),
    inference(superposition,[],[f58,f164])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f665,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f151,f96])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3))
      | ~ r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X2),X3) ) ),
    inference(subsumption_resolution,[],[f150,f53])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3))
      | ~ r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X2),X3)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f149,f54])).

fof(f149,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3))
      | ~ r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X2),X3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f144,f56])).

fof(f144,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3))
      | ~ v2_funct_1(sK1)
      | ~ r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X2),X3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f73,f95])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:40:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (13735)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.53  % (13743)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.19/0.53  % (13734)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.53  % (13729)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.54  % (13753)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.54  % (13752)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.54  % (13733)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.54  % (13732)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.54  % (13750)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.54  % (13755)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (13744)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.54  % (13741)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.54  % (13730)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.54  % (13740)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.54  % (13758)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.55  % (13746)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.31/0.55  % (13731)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.55  % (13736)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.55  % (13754)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.55  % (13757)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.55  % (13739)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.55  % (13756)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.55  % (13737)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.56  % (13751)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.56  % (13738)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.31/0.56  % (13742)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.56  % (13749)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.56  % (13747)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.56  % (13748)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.57  % (13745)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.07/0.67  % (13743)Refutation found. Thanks to Tanya!
% 2.07/0.67  % SZS status Theorem for theBenchmark
% 2.07/0.67  % SZS output start Proof for theBenchmark
% 2.07/0.67  fof(f2199,plain,(
% 2.07/0.67    $false),
% 2.07/0.67    inference(subsumption_resolution,[],[f2188,f141])).
% 2.07/0.67  fof(f141,plain,(
% 2.07/0.67    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.07/0.67    inference(subsumption_resolution,[],[f139,f57])).
% 2.07/0.67  fof(f57,plain,(
% 2.07/0.67    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 2.07/0.67    inference(cnf_transformation,[],[f49])).
% 2.07/0.68  fof(f49,plain,(
% 2.07/0.68    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.07/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f48])).
% 2.07/0.68  fof(f48,plain,(
% 2.07/0.68    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.07/0.68    introduced(choice_axiom,[])).
% 2.07/0.68  fof(f28,plain,(
% 2.07/0.68    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.07/0.68    inference(flattening,[],[f27])).
% 2.07/0.68  fof(f27,plain,(
% 2.07/0.68    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.07/0.68    inference(ennf_transformation,[],[f26])).
% 2.07/0.68  fof(f26,negated_conjecture,(
% 2.07/0.68    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 2.07/0.68    inference(negated_conjecture,[],[f25])).
% 2.07/0.68  fof(f25,conjecture,(
% 2.07/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 2.07/0.68  fof(f139,plain,(
% 2.07/0.68    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.07/0.68    inference(resolution,[],[f105,f62])).
% 2.07/0.68  fof(f62,plain,(
% 2.07/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f52])).
% 2.07/0.68  fof(f52,plain,(
% 2.07/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.68    inference(flattening,[],[f51])).
% 2.07/0.68  fof(f51,plain,(
% 2.07/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.68    inference(nnf_transformation,[],[f2])).
% 2.07/0.68  fof(f2,axiom,(
% 2.07/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.07/0.68  fof(f105,plain,(
% 2.07/0.68    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.07/0.68    inference(subsumption_resolution,[],[f101,f53])).
% 2.07/0.68  fof(f53,plain,(
% 2.07/0.68    v1_relat_1(sK1)),
% 2.07/0.68    inference(cnf_transformation,[],[f49])).
% 2.07/0.68  fof(f101,plain,(
% 2.07/0.68    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 2.07/0.68    inference(resolution,[],[f55,f71])).
% 2.07/0.68  fof(f71,plain,(
% 2.07/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f37])).
% 2.07/0.68  fof(f37,plain,(
% 2.07/0.68    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.07/0.68    inference(flattening,[],[f36])).
% 2.07/0.68  fof(f36,plain,(
% 2.07/0.68    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.07/0.68    inference(ennf_transformation,[],[f22])).
% 2.07/0.68  fof(f22,axiom,(
% 2.07/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.07/0.68  fof(f55,plain,(
% 2.07/0.68    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.07/0.68    inference(cnf_transformation,[],[f49])).
% 2.07/0.68  fof(f2188,plain,(
% 2.07/0.68    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.07/0.68    inference(resolution,[],[f665,f1855])).
% 2.07/0.68  fof(f1855,plain,(
% 2.07/0.68    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 2.07/0.68    inference(forward_demodulation,[],[f1854,f87])).
% 2.07/0.68  fof(f87,plain,(
% 2.07/0.68    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.07/0.68    inference(resolution,[],[f53,f72])).
% 2.07/0.68  fof(f72,plain,(
% 2.07/0.68    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 2.07/0.68    inference(cnf_transformation,[],[f38])).
% 2.07/0.68  fof(f38,plain,(
% 2.07/0.68    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.07/0.68    inference(ennf_transformation,[],[f18])).
% 2.07/0.68  fof(f18,axiom,(
% 2.07/0.68    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.07/0.68  fof(f1854,plain,(
% 2.07/0.68    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 2.07/0.68    inference(subsumption_resolution,[],[f1838,f855])).
% 2.07/0.68  fof(f855,plain,(
% 2.07/0.68    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.07/0.68    inference(backward_demodulation,[],[f438,f852])).
% 2.07/0.68  fof(f852,plain,(
% 2.07/0.68    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1))),
% 2.07/0.68    inference(resolution,[],[f845,f59])).
% 2.07/0.68  fof(f59,plain,(
% 2.07/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.07/0.68    inference(cnf_transformation,[],[f50])).
% 2.07/0.68  fof(f50,plain,(
% 2.07/0.68    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.07/0.68    inference(nnf_transformation,[],[f3])).
% 2.07/0.68  fof(f3,axiom,(
% 2.07/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.07/0.68  fof(f845,plain,(
% 2.07/0.68    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1))),
% 2.07/0.68    inference(forward_demodulation,[],[f835,f87])).
% 2.07/0.68  fof(f835,plain,(
% 2.07/0.68    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 2.07/0.68    inference(superposition,[],[f401,f190])).
% 2.07/0.68  fof(f190,plain,(
% 2.07/0.68    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))),
% 2.07/0.68    inference(superposition,[],[f108,f145])).
% 2.07/0.68  fof(f145,plain,(
% 2.07/0.68    k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))),
% 2.07/0.68    inference(forward_demodulation,[],[f142,f86])).
% 2.07/0.68  fof(f86,plain,(
% 2.07/0.68    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 2.07/0.68    inference(resolution,[],[f53,f75])).
% 2.07/0.68  fof(f75,plain,(
% 2.07/0.68    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f43])).
% 2.07/0.68  fof(f43,plain,(
% 2.07/0.68    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.68    inference(ennf_transformation,[],[f17])).
% 2.07/0.68  fof(f17,axiom,(
% 2.07/0.68    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.07/0.68  fof(f142,plain,(
% 2.07/0.68    k9_relat_1(sK1,k1_relat_1(sK1)) = k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))),
% 2.07/0.68    inference(superposition,[],[f95,f87])).
% 2.07/0.68  fof(f95,plain,(
% 2.07/0.68    ( ! [X3] : (k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k3_xboole_0(X3,k2_relat_1(sK1))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f94,f86])).
% 2.07/0.68  fof(f94,plain,(
% 2.07/0.68    ( ! [X3] : (k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k3_xboole_0(X3,k9_relat_1(sK1,k1_relat_1(sK1)))) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f90,f53])).
% 2.07/0.68  fof(f90,plain,(
% 2.07/0.68    ( ! [X3] : (k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k3_xboole_0(X3,k9_relat_1(sK1,k1_relat_1(sK1))) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(resolution,[],[f54,f63])).
% 2.07/0.68  fof(f63,plain,(
% 2.07/0.68    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f30])).
% 2.07/0.68  fof(f30,plain,(
% 2.07/0.68    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.07/0.68    inference(flattening,[],[f29])).
% 2.07/0.68  fof(f29,plain,(
% 2.07/0.68    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.07/0.68    inference(ennf_transformation,[],[f23])).
% 2.07/0.68  fof(f23,axiom,(
% 2.07/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 2.07/0.68  fof(f54,plain,(
% 2.07/0.68    v1_funct_1(sK1)),
% 2.07/0.68    inference(cnf_transformation,[],[f49])).
% 2.07/0.68  fof(f108,plain,(
% 2.07/0.68    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,k2_relat_1(sK1)),X3)) )),
% 2.07/0.68    inference(resolution,[],[f96,f59])).
% 2.07/0.68  fof(f96,plain,(
% 2.07/0.68    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k2_relat_1(sK1)),X0)) )),
% 2.07/0.68    inference(backward_demodulation,[],[f91,f95])).
% 2.07/0.68  fof(f91,plain,(
% 2.07/0.68    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f88,f53])).
% 2.07/0.68  fof(f88,plain,(
% 2.07/0.68    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(resolution,[],[f54,f70])).
% 2.07/0.68  fof(f70,plain,(
% 2.07/0.68    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f35])).
% 2.07/0.68  fof(f35,plain,(
% 2.07/0.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.07/0.68    inference(flattening,[],[f34])).
% 2.07/0.68  fof(f34,plain,(
% 2.07/0.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.07/0.68    inference(ennf_transformation,[],[f21])).
% 2.07/0.68  fof(f21,axiom,(
% 2.07/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 2.07/0.68  fof(f401,plain,(
% 2.07/0.68    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK1,k4_xboole_0(X0,X1)),k10_relat_1(sK1,X0))) )),
% 2.07/0.68    inference(superposition,[],[f79,f164])).
% 2.07/0.68  fof(f164,plain,(
% 2.07/0.68    ( ! [X2,X3] : (k4_xboole_0(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) = k10_relat_1(sK1,k4_xboole_0(X2,X3))) )),
% 2.07/0.68    inference(superposition,[],[f93,f82])).
% 2.07/0.68  fof(f82,plain,(
% 2.07/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f15])).
% 2.07/0.68  fof(f15,axiom,(
% 2.07/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.07/0.68  fof(f93,plain,(
% 2.07/0.68    ( ! [X2,X1] : (k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2)) = k10_relat_1(sK1,k4_xboole_0(X1,X2))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f92,f82])).
% 2.07/0.68  fof(f92,plain,(
% 2.07/0.68    ( ! [X2,X1] : (k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2))) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f89,f53])).
% 2.07/0.68  fof(f89,plain,(
% 2.07/0.68    ( ! [X2,X1] : (k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2)) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(resolution,[],[f54,f69])).
% 2.07/0.68  fof(f69,plain,(
% 2.07/0.68    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f33])).
% 2.07/0.68  fof(f33,plain,(
% 2.07/0.68    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.07/0.68    inference(flattening,[],[f32])).
% 2.07/0.68  fof(f32,plain,(
% 2.07/0.68    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.07/0.68    inference(ennf_transformation,[],[f20])).
% 2.07/0.68  fof(f20,axiom,(
% 2.07/0.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 2.07/0.68  fof(f79,plain,(
% 2.07/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f7])).
% 2.07/0.68  fof(f7,axiom,(
% 2.07/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.07/0.68  fof(f438,plain,(
% 2.07/0.68    k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k1_relat_1(sK1))),
% 2.07/0.68    inference(superposition,[],[f167,f68])).
% 2.07/0.68  fof(f68,plain,(
% 2.07/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f12])).
% 2.07/0.68  fof(f12,axiom,(
% 2.07/0.68    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.07/0.68  fof(f167,plain,(
% 2.07/0.68    ( ! [X0] : (k10_relat_1(sK1,k4_xboole_0(X0,k2_relat_1(sK1))) = k4_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f163,f82])).
% 2.07/0.68  fof(f163,plain,(
% 2.07/0.68    ( ! [X0] : (k10_relat_1(sK1,k4_xboole_0(X0,k2_relat_1(sK1))) = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.07/0.68    inference(superposition,[],[f93,f87])).
% 2.07/0.68  fof(f1838,plain,(
% 2.07/0.68    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 2.07/0.68    inference(superposition,[],[f403,f534])).
% 2.07/0.68  fof(f534,plain,(
% 2.07/0.68    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 2.07/0.68    inference(forward_demodulation,[],[f514,f526])).
% 2.07/0.68  fof(f526,plain,(
% 2.07/0.68    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 2.07/0.68    inference(forward_demodulation,[],[f525,f430])).
% 2.07/0.68  fof(f430,plain,(
% 2.07/0.68    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_relat_1(sK1),X4),k2_relat_1(sK1))) )),
% 2.07/0.68    inference(resolution,[],[f375,f59])).
% 2.07/0.68  fof(f375,plain,(
% 2.07/0.68    ( ! [X5] : (r1_tarski(k3_xboole_0(k2_relat_1(sK1),X5),k2_relat_1(sK1))) )),
% 2.07/0.68    inference(superposition,[],[f242,f145])).
% 2.07/0.68  fof(f242,plain,(
% 2.07/0.68    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,k2_relat_1(sK1)),X2),X1)) )),
% 2.07/0.68    inference(superposition,[],[f202,f65])).
% 2.07/0.68  fof(f65,plain,(
% 2.07/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.07/0.68    inference(cnf_transformation,[],[f11])).
% 2.07/0.68  fof(f11,axiom,(
% 2.07/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.07/0.68  fof(f202,plain,(
% 2.07/0.68    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(k3_xboole_0(X4,k2_relat_1(sK1)),X5),X4)) )),
% 2.07/0.68    inference(resolution,[],[f106,f79])).
% 2.07/0.68  fof(f106,plain,(
% 2.07/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,k2_relat_1(sK1))) | r1_tarski(X0,X1)) )),
% 2.07/0.68    inference(resolution,[],[f96,f76])).
% 2.07/0.68  fof(f76,plain,(
% 2.07/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f45])).
% 2.07/0.68  fof(f45,plain,(
% 2.07/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.07/0.68    inference(flattening,[],[f44])).
% 2.07/0.68  fof(f44,plain,(
% 2.07/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.07/0.68    inference(ennf_transformation,[],[f5])).
% 2.07/0.68  fof(f5,axiom,(
% 2.07/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.07/0.68  fof(f525,plain,(
% 2.07/0.68    k9_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k2_relat_1(sK1))),k2_relat_1(sK1))),
% 2.07/0.68    inference(forward_demodulation,[],[f510,f492])).
% 2.07/0.68  fof(f492,plain,(
% 2.07/0.68    ( ! [X0] : (k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k3_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,X0))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f491,f65])).
% 2.07/0.68  fof(f491,plain,(
% 2.07/0.68    ( ! [X0] : (k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,X0)))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f481,f176])).
% 2.07/0.68  fof(f176,plain,(
% 2.07/0.68    ( ! [X0] : (k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,X0))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f170,f82])).
% 2.07/0.68  fof(f170,plain,(
% 2.07/0.68    ( ! [X0] : (k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X0))) )),
% 2.07/0.68    inference(superposition,[],[f100,f86])).
% 2.07/0.68  fof(f100,plain,(
% 2.07/0.68    ( ! [X0,X1] : (k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f99,f82])).
% 2.07/0.68  fof(f99,plain,(
% 2.07/0.68    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f98,f53])).
% 2.07/0.68  fof(f98,plain,(
% 2.07/0.68    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f97,f54])).
% 2.07/0.68  fof(f97,plain,(
% 2.07/0.68    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(resolution,[],[f56,f74])).
% 2.07/0.68  fof(f74,plain,(
% 2.07/0.68    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f42])).
% 2.07/0.68  fof(f42,plain,(
% 2.07/0.68    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.07/0.68    inference(flattening,[],[f41])).
% 2.07/0.68  fof(f41,plain,(
% 2.07/0.68    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.07/0.68    inference(ennf_transformation,[],[f19])).
% 2.07/0.68  fof(f19,axiom,(
% 2.07/0.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 2.07/0.68  fof(f56,plain,(
% 2.07/0.68    v2_funct_1(sK1)),
% 2.07/0.68    inference(cnf_transformation,[],[f49])).
% 2.07/0.68  fof(f481,plain,(
% 2.07/0.68    ( ! [X0] : (k4_xboole_0(k2_relat_1(sK1),k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0))) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) )),
% 2.07/0.68    inference(superposition,[],[f176,f65])).
% 2.07/0.68  fof(f510,plain,(
% 2.07/0.68    k9_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),k2_relat_1(sK1))),
% 2.07/0.68    inference(superposition,[],[f177,f108])).
% 2.07/0.68  fof(f177,plain,(
% 2.07/0.68    ( ! [X0] : (k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k4_xboole_0(k9_relat_1(sK1,X0),k2_relat_1(sK1))) )),
% 2.07/0.68    inference(forward_demodulation,[],[f172,f82])).
% 2.07/0.68  fof(f172,plain,(
% 2.07/0.68    ( ! [X0] : (k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k6_subset_1(k9_relat_1(sK1,X0),k2_relat_1(sK1))) )),
% 2.07/0.68    inference(superposition,[],[f100,f86])).
% 2.07/0.68  fof(f514,plain,(
% 2.07/0.68    k9_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 2.07/0.68    inference(superposition,[],[f177,f104])).
% 2.07/0.68  fof(f104,plain,(
% 2.07/0.68    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 2.07/0.68    inference(resolution,[],[f55,f59])).
% 2.07/0.68  fof(f403,plain,(
% 2.07/0.68    ( ! [X4,X5] : (k1_xboole_0 != k10_relat_1(sK1,k4_xboole_0(X4,X5)) | r1_tarski(k10_relat_1(sK1,X4),k10_relat_1(sK1,X5))) )),
% 2.07/0.68    inference(superposition,[],[f58,f164])).
% 2.07/0.68  fof(f58,plain,(
% 2.07/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f50])).
% 2.07/0.68  fof(f665,plain,(
% 2.07/0.68    ( ! [X0] : (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 2.07/0.68    inference(resolution,[],[f151,f96])).
% 2.07/0.68  fof(f151,plain,(
% 2.07/0.68    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3)) | ~r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X2),X3)) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f150,f53])).
% 2.07/0.68  fof(f150,plain,(
% 2.07/0.68    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3)) | ~r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X2),X3) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f149,f54])).
% 2.07/0.68  fof(f149,plain,(
% 2.07/0.68    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3)) | ~r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X2),X3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(subsumption_resolution,[],[f144,f56])).
% 2.07/0.68  fof(f144,plain,(
% 2.07/0.68    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,k2_relat_1(sK1)),k9_relat_1(sK1,X3)) | ~v2_funct_1(sK1) | ~r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X2),X3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.07/0.68    inference(superposition,[],[f73,f95])).
% 2.07/0.68  fof(f73,plain,(
% 2.07/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.07/0.68    inference(cnf_transformation,[],[f40])).
% 2.07/0.68  fof(f40,plain,(
% 2.07/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.07/0.68    inference(flattening,[],[f39])).
% 2.07/0.68  fof(f39,plain,(
% 2.07/0.68    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.07/0.68    inference(ennf_transformation,[],[f24])).
% 2.07/0.68  fof(f24,axiom,(
% 2.07/0.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.07/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 2.07/0.68  % SZS output end Proof for theBenchmark
% 2.07/0.68  % (13743)------------------------------
% 2.07/0.68  % (13743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.68  % (13743)Termination reason: Refutation
% 2.07/0.68  
% 2.07/0.68  % (13743)Memory used [KB]: 3326
% 2.07/0.68  % (13743)Time elapsed: 0.241 s
% 2.07/0.68  % (13743)------------------------------
% 2.07/0.68  % (13743)------------------------------
% 2.07/0.68  % (13728)Success in time 0.319 s
%------------------------------------------------------------------------------
