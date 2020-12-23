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
% DateTime   : Thu Dec  3 12:54:06 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 160 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  193 ( 404 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3788,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3751])).

fof(f3751,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f102,f3678])).

fof(f3678,plain,(
    ! [X7] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X7)),X7) ),
    inference(resolution,[],[f3673,f159])).

fof(f159,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3673,plain,(
    ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3672,f2185])).

fof(f2185,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2150,f117])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(resolution,[],[f72,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2150,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f1868,f117])).

fof(f1868,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f1867,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f1867,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f3672,plain,(
    ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f3651,f1462])).

fof(f1462,plain,(
    ! [X10,X9] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X9),X10),k1_relat_1(sK1)) ),
    inference(superposition,[],[f100,f1418])).

fof(f1418,plain,(
    ! [X6] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X6),k1_relat_1(sK1)) ),
    inference(resolution,[],[f1411,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1411,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f1409])).

fof(f1409,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f1371,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1371,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),X1) ) ),
    inference(resolution,[],[f1370,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1370,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f1369,f36])).

fof(f1369,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f75,f37])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f100,plain,(
    ! [X6,X4,X5] : r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6)) ),
    inference(superposition,[],[f92,f82])).

fof(f82,plain,(
    ! [X2,X3] : k2_xboole_0(k6_subset_1(X2,X3),X2) = X2 ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f92,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f3651,plain,(
    ! [X11] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f825,f3213])).

fof(f3213,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    inference(superposition,[],[f3120,f516])).

fof(f516,plain,(
    ! [X2] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2) ),
    inference(resolution,[],[f513,f72])).

fof(f513,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f512,f36])).

fof(f512,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f3120,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f3119,f36])).

fof(f3119,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f3118,f37])).

fof(f3118,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f66,f38])).

fof(f38,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f825,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f102,plain,(
    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (12115)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (12125)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (12108)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (12115)Refutation not found, incomplete strategy% (12115)------------------------------
% 0.20/0.51  % (12115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12117)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (12124)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (12116)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (12109)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (12123)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (12115)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12115)Memory used [KB]: 10618
% 0.20/0.52  % (12115)Time elapsed: 0.100 s
% 0.20/0.52  % (12115)------------------------------
% 0.20/0.52  % (12115)------------------------------
% 0.20/0.53  % (12114)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (12133)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (12122)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (12130)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (12105)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (12118)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (12114)Refutation not found, incomplete strategy% (12114)------------------------------
% 0.20/0.54  % (12114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12114)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12114)Memory used [KB]: 10618
% 0.20/0.54  % (12114)Time elapsed: 0.124 s
% 0.20/0.54  % (12114)------------------------------
% 0.20/0.54  % (12114)------------------------------
% 0.20/0.54  % (12107)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (12106)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (12104)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (12121)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (12121)Refutation not found, incomplete strategy% (12121)------------------------------
% 0.20/0.55  % (12121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12121)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12121)Memory used [KB]: 10618
% 0.20/0.55  % (12121)Time elapsed: 0.150 s
% 0.20/0.55  % (12121)------------------------------
% 0.20/0.55  % (12121)------------------------------
% 0.20/0.55  % (12120)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (12110)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (12129)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (12113)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (12112)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (12126)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (12126)Refutation not found, incomplete strategy% (12126)------------------------------
% 0.20/0.57  % (12126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (12126)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (12126)Memory used [KB]: 10746
% 0.20/0.57  % (12126)Time elapsed: 0.153 s
% 0.20/0.57  % (12126)------------------------------
% 0.20/0.57  % (12126)------------------------------
% 0.20/0.57  % (12127)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (12132)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (12128)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.58  % (12119)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.58  % (12111)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.58  % (12131)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.06/0.66  % (12134)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.06/0.66  % (12134)Refutation not found, incomplete strategy% (12134)------------------------------
% 2.06/0.66  % (12134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.66  % (12134)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.66  
% 2.06/0.66  % (12134)Memory used [KB]: 6140
% 2.06/0.66  % (12134)Time elapsed: 0.111 s
% 2.06/0.66  % (12134)------------------------------
% 2.06/0.66  % (12134)------------------------------
% 2.06/0.68  % (12135)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.06/0.69  % (12137)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.76/0.72  % (12110)Refutation found. Thanks to Tanya!
% 2.76/0.72  % SZS status Theorem for theBenchmark
% 2.76/0.72  % SZS output start Proof for theBenchmark
% 2.76/0.72  fof(f3788,plain,(
% 2.76/0.72    $false),
% 2.76/0.72    inference(trivial_inequality_removal,[],[f3751])).
% 2.76/0.72  fof(f3751,plain,(
% 2.76/0.72    k1_xboole_0 != k1_xboole_0),
% 2.76/0.72    inference(superposition,[],[f102,f3678])).
% 2.76/0.72  fof(f3678,plain,(
% 2.76/0.72    ( ! [X7] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X7)),X7)) )),
% 2.76/0.72    inference(resolution,[],[f3673,f159])).
% 2.76/0.72  fof(f159,plain,(
% 2.76/0.72    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.76/0.72    inference(resolution,[],[f58,f40])).
% 2.76/0.72  fof(f40,plain,(
% 2.76/0.72    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f6])).
% 2.76/0.72  fof(f6,axiom,(
% 2.76/0.72    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.76/0.72  fof(f58,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.76/0.72    inference(cnf_transformation,[],[f2])).
% 2.76/0.72  fof(f2,axiom,(
% 2.76/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.76/0.72  fof(f3673,plain,(
% 2.76/0.72    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) )),
% 2.76/0.72    inference(forward_demodulation,[],[f3672,f2185])).
% 2.76/0.72  fof(f2185,plain,(
% 2.76/0.72    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.76/0.72    inference(forward_demodulation,[],[f2150,f117])).
% 2.76/0.72  fof(f117,plain,(
% 2.76/0.72    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 2.76/0.72    inference(resolution,[],[f72,f76])).
% 2.76/0.72  fof(f76,plain,(
% 2.76/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.76/0.72    inference(equality_resolution,[],[f57])).
% 2.76/0.72  fof(f57,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.76/0.72    inference(cnf_transformation,[],[f2])).
% 2.76/0.72  fof(f72,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.76/0.72    inference(definition_unfolding,[],[f62,f51])).
% 2.76/0.72  fof(f51,plain,(
% 2.76/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f12])).
% 2.76/0.72  fof(f12,axiom,(
% 2.76/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.76/0.72  fof(f62,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.76/0.72    inference(cnf_transformation,[],[f3])).
% 2.76/0.72  fof(f3,axiom,(
% 2.76/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.76/0.72  fof(f2150,plain,(
% 2.76/0.72    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 2.76/0.72    inference(superposition,[],[f1868,f117])).
% 2.76/0.72  fof(f1868,plain,(
% 2.76/0.72    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f1867,f36])).
% 2.76/0.72  fof(f36,plain,(
% 2.76/0.72    v1_relat_1(sK1)),
% 2.76/0.72    inference(cnf_transformation,[],[f21])).
% 2.76/0.72  fof(f21,plain,(
% 2.76/0.72    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.76/0.72    inference(flattening,[],[f20])).
% 2.76/0.72  fof(f20,plain,(
% 2.76/0.72    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.76/0.72    inference(ennf_transformation,[],[f19])).
% 2.76/0.72  fof(f19,negated_conjecture,(
% 2.76/0.72    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.76/0.72    inference(negated_conjecture,[],[f18])).
% 2.76/0.72  fof(f18,conjecture,(
% 2.76/0.72    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 2.76/0.72  fof(f1867,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~v1_relat_1(sK1) | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 2.76/0.72    inference(resolution,[],[f65,f37])).
% 2.76/0.72  fof(f37,plain,(
% 2.76/0.72    v1_funct_1(sK1)),
% 2.76/0.72    inference(cnf_transformation,[],[f21])).
% 2.76/0.72  fof(f65,plain,(
% 2.76/0.72    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 2.76/0.72    inference(cnf_transformation,[],[f33])).
% 2.76/0.72  fof(f33,plain,(
% 2.76/0.72    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.76/0.72    inference(flattening,[],[f32])).
% 2.76/0.72  fof(f32,plain,(
% 2.76/0.72    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.76/0.72    inference(ennf_transformation,[],[f15])).
% 2.76/0.72  fof(f15,axiom,(
% 2.76/0.72    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 2.76/0.72  fof(f3672,plain,(
% 2.76/0.72    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f3651,f1462])).
% 2.76/0.72  fof(f1462,plain,(
% 2.76/0.72    ( ! [X10,X9] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X9),X10),k1_relat_1(sK1))) )),
% 2.76/0.72    inference(superposition,[],[f100,f1418])).
% 2.76/0.72  fof(f1418,plain,(
% 2.76/0.72    ( ! [X6] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X6),k1_relat_1(sK1))) )),
% 2.76/0.72    inference(resolution,[],[f1411,f53])).
% 2.76/0.72  fof(f53,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.76/0.72    inference(cnf_transformation,[],[f26])).
% 2.76/0.72  fof(f26,plain,(
% 2.76/0.72    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.76/0.72    inference(ennf_transformation,[],[f5])).
% 2.76/0.72  fof(f5,axiom,(
% 2.76/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.76/0.72  fof(f1411,plain,(
% 2.76/0.72    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.76/0.72    inference(duplicate_literal_removal,[],[f1409])).
% 2.76/0.72  fof(f1409,plain,(
% 2.76/0.72    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.76/0.72    inference(resolution,[],[f1371,f61])).
% 2.76/0.72  fof(f61,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f30])).
% 2.76/0.72  fof(f30,plain,(
% 2.76/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.76/0.72    inference(ennf_transformation,[],[f1])).
% 2.76/0.72  fof(f1,axiom,(
% 2.76/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.76/0.72  fof(f1371,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),X1)) )),
% 2.76/0.72    inference(resolution,[],[f1370,f60])).
% 2.76/0.72  fof(f60,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f30])).
% 2.76/0.72  fof(f1370,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f1369,f36])).
% 2.76/0.72  fof(f1369,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 2.76/0.72    inference(resolution,[],[f75,f37])).
% 2.76/0.72  fof(f75,plain,(
% 2.76/0.72    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 2.76/0.72    inference(equality_resolution,[],[f46])).
% 2.76/0.72  fof(f46,plain,(
% 2.76/0.72    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.76/0.72    inference(cnf_transformation,[],[f23])).
% 2.76/0.72  fof(f23,plain,(
% 2.76/0.72    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/0.72    inference(flattening,[],[f22])).
% 2.76/0.72  fof(f22,plain,(
% 2.76/0.72    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/0.72    inference(ennf_transformation,[],[f13])).
% 2.76/0.72  fof(f13,axiom,(
% 2.76/0.72    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 2.76/0.72  fof(f100,plain,(
% 2.76/0.72    ( ! [X6,X4,X5] : (r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))) )),
% 2.76/0.72    inference(superposition,[],[f92,f82])).
% 2.76/0.72  fof(f82,plain,(
% 2.76/0.72    ( ! [X2,X3] : (k2_xboole_0(k6_subset_1(X2,X3),X2) = X2) )),
% 2.76/0.72    inference(resolution,[],[f53,f69])).
% 2.76/0.72  fof(f69,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.76/0.72    inference(definition_unfolding,[],[f50,f51])).
% 2.76/0.72  fof(f50,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f7])).
% 2.76/0.72  fof(f7,axiom,(
% 2.76/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.76/0.72  fof(f92,plain,(
% 2.76/0.72    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 2.76/0.72    inference(resolution,[],[f64,f49])).
% 2.76/0.72  fof(f49,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.76/0.72    inference(cnf_transformation,[],[f11])).
% 2.76/0.72  fof(f11,axiom,(
% 2.76/0.72    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.76/0.72  fof(f64,plain,(
% 2.76/0.72    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f31])).
% 2.76/0.72  fof(f31,plain,(
% 2.76/0.72    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.76/0.72    inference(ennf_transformation,[],[f4])).
% 2.76/0.72  fof(f4,axiom,(
% 2.76/0.72    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.76/0.72  fof(f3651,plain,(
% 2.76/0.72    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1))) )),
% 2.76/0.72    inference(superposition,[],[f825,f3213])).
% 2.76/0.72  fof(f3213,plain,(
% 2.76/0.72    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) )),
% 2.76/0.72    inference(superposition,[],[f3120,f516])).
% 2.76/0.72  fof(f516,plain,(
% 2.76/0.72    ( ! [X2] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2)) )),
% 2.76/0.72    inference(resolution,[],[f513,f72])).
% 2.76/0.72  fof(f513,plain,(
% 2.76/0.72    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f512,f36])).
% 2.76/0.72  fof(f512,plain,(
% 2.76/0.72    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.76/0.72    inference(resolution,[],[f55,f37])).
% 2.76/0.72  fof(f55,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 2.76/0.72    inference(cnf_transformation,[],[f29])).
% 2.76/0.72  fof(f29,plain,(
% 2.76/0.72    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.76/0.72    inference(flattening,[],[f28])).
% 2.76/0.72  fof(f28,plain,(
% 2.76/0.72    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.76/0.72    inference(ennf_transformation,[],[f16])).
% 2.76/0.72  fof(f16,axiom,(
% 2.76/0.72    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 2.76/0.72  fof(f3120,plain,(
% 2.76/0.72    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f3119,f36])).
% 2.76/0.72  fof(f3119,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~v1_relat_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 2.76/0.72    inference(subsumption_resolution,[],[f3118,f37])).
% 2.76/0.72  fof(f3118,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 2.76/0.72    inference(resolution,[],[f66,f38])).
% 2.76/0.72  fof(f38,plain,(
% 2.76/0.72    v2_funct_1(sK1)),
% 2.76/0.72    inference(cnf_transformation,[],[f21])).
% 2.76/0.72  fof(f66,plain,(
% 2.76/0.72    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 2.76/0.72    inference(cnf_transformation,[],[f35])).
% 2.76/0.72  fof(f35,plain,(
% 2.76/0.72    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.76/0.72    inference(flattening,[],[f34])).
% 2.76/0.72  fof(f34,plain,(
% 2.76/0.72    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.76/0.72    inference(ennf_transformation,[],[f14])).
% 2.76/0.72  fof(f14,axiom,(
% 2.76/0.72    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 2.76/0.72  fof(f825,plain,(
% 2.76/0.72    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 2.76/0.72    inference(resolution,[],[f52,f36])).
% 2.76/0.72  fof(f52,plain,(
% 2.76/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 2.76/0.72    inference(cnf_transformation,[],[f25])).
% 2.76/0.72  fof(f25,plain,(
% 2.76/0.72    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.76/0.72    inference(flattening,[],[f24])).
% 2.76/0.72  fof(f24,plain,(
% 2.76/0.72    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.76/0.72    inference(ennf_transformation,[],[f17])).
% 2.76/0.72  fof(f17,axiom,(
% 2.76/0.72    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.76/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.76/0.72  fof(f102,plain,(
% 2.76/0.72    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.76/0.72    inference(resolution,[],[f71,f39])).
% 2.76/0.72  fof(f39,plain,(
% 2.76/0.72    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.76/0.72    inference(cnf_transformation,[],[f21])).
% 2.76/0.72  fof(f71,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 2.76/0.72    inference(definition_unfolding,[],[f63,f51])).
% 2.76/0.72  fof(f63,plain,(
% 2.76/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.76/0.72    inference(cnf_transformation,[],[f3])).
% 2.76/0.72  % SZS output end Proof for theBenchmark
% 2.76/0.72  % (12110)------------------------------
% 2.76/0.72  % (12110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.72  % (12110)Termination reason: Refutation
% 2.76/0.72  
% 2.76/0.72  % (12110)Memory used [KB]: 8443
% 2.76/0.72  % (12110)Time elapsed: 0.314 s
% 2.76/0.72  % (12110)------------------------------
% 2.76/0.72  % (12110)------------------------------
% 2.76/0.73  % (12103)Success in time 0.357 s
%------------------------------------------------------------------------------
