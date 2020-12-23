%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:06 EST 2020

% Result     : Theorem 3.03s
% Output     : Refutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 176 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  211 ( 450 expanded)
%              Number of equality atoms :   42 (  65 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6892,plain,(
    $false ),
    inference(resolution,[],[f6841,f38])).

fof(f38,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f6841,plain,(
    ! [X28] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X28)),X28) ),
    inference(trivial_inequality_removal,[],[f6808])).

fof(f6808,plain,(
    ! [X28] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X28)),X28) ) ),
    inference(superposition,[],[f66,f6650])).

fof(f6650,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(resolution,[],[f6649,f187])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6649,plain,(
    ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0) ),
    inference(forward_demodulation,[],[f6648,f2279])).

fof(f2279,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2228,f117])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(resolution,[],[f67,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2228,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0)) ),
    inference(resolution,[],[f2220,f71])).

fof(f2220,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9)) ) ),
    inference(backward_demodulation,[],[f800,f2219])).

fof(f2219,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f2218,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f2218,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f800,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9)) ) ),
    inference(resolution,[],[f796,f67])).

fof(f796,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f60,f35])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f6648,plain,(
    ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f6630,f1982])).

fof(f1982,plain,(
    ! [X17,X16] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X16),X17),k1_relat_1(sK1)) ),
    inference(superposition,[],[f93,f1916])).

fof(f1916,plain,(
    ! [X1] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f1913,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1913,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f1911])).

fof(f1911,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f1616,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1616,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),X1) ) ),
    inference(resolution,[],[f1615,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1615,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f1614,f35])).

fof(f1614,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f70,f36])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f93,plain,(
    ! [X6,X4,X5] : r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6)) ),
    inference(superposition,[],[f85,f76])).

fof(f76,plain,(
    ! [X2,X3] : k2_xboole_0(k6_subset_1(X2,X3),X2) = X2 ),
    inference(resolution,[],[f50,f65])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f85,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f80,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f61,f71])).

fof(f6630,plain,(
    ! [X11] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f1354,f6040])).

fof(f6040,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    inference(superposition,[],[f3370,f501])).

fof(f501,plain,(
    ! [X5] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5) ),
    inference(resolution,[],[f497,f67])).

fof(f497,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f496,f35])).

fof(f496,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f51,f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f3370,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f3369,f35])).

fof(f3369,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f3368,f36])).

fof(f3368,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f63,f37])).

fof(f37,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f1354,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (23701)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (23698)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (23717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (23708)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.51  % (23709)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.51  % (23713)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.21/0.51  % (23717)Refutation not found, incomplete strategy% (23717)------------------------------
% 1.21/0.51  % (23717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.51  % (23717)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.51  
% 1.21/0.51  % (23717)Memory used [KB]: 10746
% 1.21/0.51  % (23717)Time elapsed: 0.082 s
% 1.21/0.51  % (23717)------------------------------
% 1.21/0.51  % (23717)------------------------------
% 1.21/0.52  % (23705)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.21/0.52  % (23699)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.52  % (23700)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.52  % (23721)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.21/0.52  % (23706)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.52  % (23704)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.21/0.52  % (23703)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.52  % (23722)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.21/0.53  % (23718)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.53  % (23712)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.21/0.53  % (23695)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.53  % (23714)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.53  % (23697)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.53  % (23724)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.53  % (23712)Refutation not found, incomplete strategy% (23712)------------------------------
% 1.36/0.53  % (23712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (23712)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (23712)Memory used [KB]: 10618
% 1.36/0.53  % (23712)Time elapsed: 0.120 s
% 1.36/0.53  % (23712)------------------------------
% 1.36/0.53  % (23712)------------------------------
% 1.36/0.54  % (23696)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (23715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (23710)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (23719)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (23716)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (23711)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (23723)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (23702)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (23707)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.57  % (23720)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.62  % (23742)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.02/0.69  % (23743)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.03/0.79  % (23701)Refutation found. Thanks to Tanya!
% 3.03/0.79  % SZS status Theorem for theBenchmark
% 3.03/0.79  % SZS output start Proof for theBenchmark
% 3.03/0.79  fof(f6892,plain,(
% 3.03/0.79    $false),
% 3.03/0.79    inference(resolution,[],[f6841,f38])).
% 3.03/0.79  fof(f38,plain,(
% 3.03/0.79    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 3.03/0.79    inference(cnf_transformation,[],[f19])).
% 3.03/0.79  fof(f19,plain,(
% 3.03/0.79    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.03/0.79    inference(flattening,[],[f18])).
% 3.03/0.79  fof(f18,plain,(
% 3.03/0.79    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.03/0.79    inference(ennf_transformation,[],[f17])).
% 3.03/0.79  fof(f17,negated_conjecture,(
% 3.03/0.79    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.03/0.79    inference(negated_conjecture,[],[f16])).
% 3.03/0.79  fof(f16,conjecture,(
% 3.03/0.79    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 3.03/0.79  fof(f6841,plain,(
% 3.03/0.79    ( ! [X28] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X28)),X28)) )),
% 3.03/0.79    inference(trivial_inequality_removal,[],[f6808])).
% 3.03/0.79  fof(f6808,plain,(
% 3.03/0.79    ( ! [X28] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X28)),X28)) )),
% 3.03/0.79    inference(superposition,[],[f66,f6650])).
% 3.03/0.79  fof(f6650,plain,(
% 3.03/0.79    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 3.03/0.79    inference(resolution,[],[f6649,f187])).
% 3.03/0.79  fof(f187,plain,(
% 3.03/0.79    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.03/0.79    inference(resolution,[],[f54,f39])).
% 3.03/0.79  fof(f39,plain,(
% 3.03/0.79    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.03/0.79    inference(cnf_transformation,[],[f6])).
% 3.03/0.79  fof(f6,axiom,(
% 3.03/0.79    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.03/0.79  fof(f54,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.03/0.79    inference(cnf_transformation,[],[f2])).
% 3.03/0.79  fof(f2,axiom,(
% 3.03/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.03/0.79  fof(f6649,plain,(
% 3.03/0.79    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) )),
% 3.03/0.79    inference(forward_demodulation,[],[f6648,f2279])).
% 3.03/0.79  fof(f2279,plain,(
% 3.03/0.79    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 3.03/0.79    inference(forward_demodulation,[],[f2228,f117])).
% 3.03/0.79  fof(f117,plain,(
% 3.03/0.79    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 3.03/0.79    inference(resolution,[],[f67,f71])).
% 3.03/0.79  fof(f71,plain,(
% 3.03/0.79    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.03/0.79    inference(equality_resolution,[],[f53])).
% 3.03/0.79  fof(f53,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.03/0.79    inference(cnf_transformation,[],[f2])).
% 3.03/0.79  fof(f67,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 3.03/0.79    inference(definition_unfolding,[],[f58,f48])).
% 3.03/0.79  fof(f48,plain,(
% 3.03/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.03/0.79    inference(cnf_transformation,[],[f9])).
% 3.03/0.79  fof(f9,axiom,(
% 3.03/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.03/0.79  fof(f58,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.03/0.79    inference(cnf_transformation,[],[f3])).
% 3.03/0.79  fof(f3,axiom,(
% 3.03/0.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.03/0.79  fof(f2228,plain,(
% 3.03/0.79    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0))) )),
% 3.03/0.79    inference(resolution,[],[f2220,f71])).
% 3.03/0.79  fof(f2220,plain,(
% 3.03/0.79    ( ! [X8,X9] : (~r1_tarski(X8,X9) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X8,X9))) )),
% 3.03/0.79    inference(backward_demodulation,[],[f800,f2219])).
% 3.03/0.79  fof(f2219,plain,(
% 3.03/0.79    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 3.03/0.79    inference(subsumption_resolution,[],[f2218,f35])).
% 3.03/0.79  fof(f35,plain,(
% 3.03/0.79    v1_relat_1(sK1)),
% 3.03/0.79    inference(cnf_transformation,[],[f19])).
% 3.03/0.79  fof(f2218,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~v1_relat_1(sK1) | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 3.03/0.79    inference(resolution,[],[f62,f36])).
% 3.03/0.79  fof(f36,plain,(
% 3.03/0.79    v1_funct_1(sK1)),
% 3.03/0.79    inference(cnf_transformation,[],[f19])).
% 3.03/0.79  fof(f62,plain,(
% 3.03/0.79    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 3.03/0.79    inference(cnf_transformation,[],[f32])).
% 3.03/0.79  fof(f32,plain,(
% 3.03/0.79    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/0.79    inference(flattening,[],[f31])).
% 3.03/0.79  fof(f31,plain,(
% 3.03/0.79    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.03/0.79    inference(ennf_transformation,[],[f13])).
% 3.03/0.79  fof(f13,axiom,(
% 3.03/0.79    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 3.03/0.79  fof(f800,plain,(
% 3.03/0.79    ( ! [X8,X9] : (~r1_tarski(X8,X9) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X9))) )),
% 3.03/0.79    inference(resolution,[],[f796,f67])).
% 3.03/0.79  fof(f796,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~r1_tarski(X0,X1)) )),
% 3.03/0.79    inference(resolution,[],[f60,f35])).
% 3.03/0.79  fof(f60,plain,(
% 3.03/0.79    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 3.03/0.79    inference(cnf_transformation,[],[f29])).
% 3.03/0.79  fof(f29,plain,(
% 3.03/0.79    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.03/0.79    inference(flattening,[],[f28])).
% 3.03/0.79  fof(f28,plain,(
% 3.03/0.79    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.03/0.79    inference(ennf_transformation,[],[f10])).
% 3.03/0.79  fof(f10,axiom,(
% 3.03/0.79    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 3.03/0.79  fof(f6648,plain,(
% 3.03/0.79    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))) )),
% 3.03/0.79    inference(subsumption_resolution,[],[f6630,f1982])).
% 3.03/0.79  fof(f1982,plain,(
% 3.03/0.79    ( ! [X17,X16] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X16),X17),k1_relat_1(sK1))) )),
% 3.03/0.79    inference(superposition,[],[f93,f1916])).
% 3.03/0.79  fof(f1916,plain,(
% 3.03/0.79    ( ! [X1] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1))) )),
% 3.03/0.79    inference(resolution,[],[f1913,f50])).
% 3.03/0.79  fof(f50,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.03/0.79    inference(cnf_transformation,[],[f24])).
% 3.03/0.79  fof(f24,plain,(
% 3.03/0.79    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.03/0.79    inference(ennf_transformation,[],[f5])).
% 3.03/0.79  fof(f5,axiom,(
% 3.03/0.79    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.03/0.79  fof(f1913,plain,(
% 3.03/0.79    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.03/0.79    inference(duplicate_literal_removal,[],[f1911])).
% 3.03/0.79  fof(f1911,plain,(
% 3.03/0.79    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.03/0.79    inference(resolution,[],[f1616,f57])).
% 3.03/0.79  fof(f57,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.03/0.79    inference(cnf_transformation,[],[f27])).
% 3.03/0.79  fof(f27,plain,(
% 3.03/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.03/0.79    inference(ennf_transformation,[],[f1])).
% 3.03/0.79  fof(f1,axiom,(
% 3.03/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.03/0.79  fof(f1616,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),X1)) )),
% 3.03/0.79    inference(resolution,[],[f1615,f56])).
% 3.03/0.79  fof(f56,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.03/0.79    inference(cnf_transformation,[],[f27])).
% 3.03/0.79  fof(f1615,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 3.03/0.79    inference(subsumption_resolution,[],[f1614,f35])).
% 3.03/0.79  fof(f1614,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 3.03/0.79    inference(resolution,[],[f70,f36])).
% 3.03/0.79  fof(f70,plain,(
% 3.03/0.79    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 3.03/0.79    inference(equality_resolution,[],[f44])).
% 3.03/0.79  fof(f44,plain,(
% 3.03/0.79    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 3.03/0.79    inference(cnf_transformation,[],[f21])).
% 3.03/0.79  fof(f21,plain,(
% 3.03/0.79    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.79    inference(flattening,[],[f20])).
% 3.03/0.79  fof(f20,plain,(
% 3.03/0.79    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/0.79    inference(ennf_transformation,[],[f11])).
% 3.03/0.79  fof(f11,axiom,(
% 3.03/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 3.03/0.79  fof(f93,plain,(
% 3.03/0.79    ( ! [X6,X4,X5] : (r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))) )),
% 3.03/0.79    inference(superposition,[],[f85,f76])).
% 3.03/0.79  fof(f76,plain,(
% 3.03/0.79    ( ! [X2,X3] : (k2_xboole_0(k6_subset_1(X2,X3),X2) = X2) )),
% 3.03/0.79    inference(resolution,[],[f50,f65])).
% 3.03/0.79  fof(f65,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.03/0.79    inference(definition_unfolding,[],[f47,f48])).
% 3.03/0.79  fof(f47,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.03/0.79    inference(cnf_transformation,[],[f7])).
% 3.03/0.79  fof(f7,axiom,(
% 3.03/0.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.03/0.79  fof(f85,plain,(
% 3.03/0.79    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 3.03/0.79    inference(resolution,[],[f80,f61])).
% 3.03/0.79  fof(f61,plain,(
% 3.03/0.79    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 3.03/0.79    inference(cnf_transformation,[],[f30])).
% 3.03/0.79  fof(f30,plain,(
% 3.03/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.03/0.79    inference(ennf_transformation,[],[f4])).
% 3.03/0.79  fof(f4,axiom,(
% 3.03/0.79    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 3.03/0.79  fof(f80,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.03/0.79    inference(resolution,[],[f61,f71])).
% 3.03/0.79  fof(f6630,plain,(
% 3.03/0.79    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1))) )),
% 3.03/0.79    inference(superposition,[],[f1354,f6040])).
% 3.03/0.79  fof(f6040,plain,(
% 3.03/0.79    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) )),
% 3.03/0.79    inference(superposition,[],[f3370,f501])).
% 3.03/0.79  fof(f501,plain,(
% 3.03/0.79    ( ! [X5] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X5)),X5)) )),
% 3.03/0.79    inference(resolution,[],[f497,f67])).
% 3.03/0.79  fof(f497,plain,(
% 3.03/0.79    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 3.03/0.79    inference(subsumption_resolution,[],[f496,f35])).
% 3.03/0.79  fof(f496,plain,(
% 3.03/0.79    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 3.03/0.79    inference(resolution,[],[f51,f36])).
% 3.03/0.79  fof(f51,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 3.03/0.79    inference(cnf_transformation,[],[f26])).
% 3.03/0.79  fof(f26,plain,(
% 3.03/0.79    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.03/0.79    inference(flattening,[],[f25])).
% 3.03/0.79  fof(f25,plain,(
% 3.03/0.79    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.03/0.79    inference(ennf_transformation,[],[f14])).
% 3.03/0.79  fof(f14,axiom,(
% 3.03/0.79    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 3.03/0.79  fof(f3370,plain,(
% 3.03/0.79    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 3.03/0.79    inference(subsumption_resolution,[],[f3369,f35])).
% 3.03/0.79  fof(f3369,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~v1_relat_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 3.03/0.79    inference(subsumption_resolution,[],[f3368,f36])).
% 3.03/0.79  fof(f3368,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 3.03/0.79    inference(resolution,[],[f63,f37])).
% 3.03/0.79  fof(f37,plain,(
% 3.03/0.79    v2_funct_1(sK1)),
% 3.03/0.79    inference(cnf_transformation,[],[f19])).
% 3.03/0.79  fof(f63,plain,(
% 3.03/0.79    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 3.03/0.79    inference(cnf_transformation,[],[f34])).
% 3.03/0.79  fof(f34,plain,(
% 3.03/0.79    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/0.79    inference(flattening,[],[f33])).
% 3.03/0.79  fof(f33,plain,(
% 3.03/0.79    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.03/0.79    inference(ennf_transformation,[],[f12])).
% 3.03/0.79  fof(f12,axiom,(
% 3.03/0.79    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 3.03/0.79  fof(f1354,plain,(
% 3.03/0.79    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 3.03/0.79    inference(resolution,[],[f49,f35])).
% 3.03/0.79  fof(f49,plain,(
% 3.03/0.79    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 3.03/0.79    inference(cnf_transformation,[],[f23])).
% 3.03/0.79  fof(f23,plain,(
% 3.03/0.79    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.03/0.79    inference(flattening,[],[f22])).
% 3.03/0.79  fof(f22,plain,(
% 3.03/0.79    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.03/0.79    inference(ennf_transformation,[],[f15])).
% 3.03/0.79  fof(f15,axiom,(
% 3.03/0.79    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.03/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 3.03/0.79  fof(f66,plain,(
% 3.03/0.79    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 3.03/0.79    inference(definition_unfolding,[],[f59,f48])).
% 3.03/0.79  fof(f59,plain,(
% 3.03/0.79    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.03/0.79    inference(cnf_transformation,[],[f3])).
% 3.03/0.79  % SZS output end Proof for theBenchmark
% 3.03/0.79  % (23701)------------------------------
% 3.03/0.79  % (23701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.79  % (23701)Termination reason: Refutation
% 3.03/0.79  
% 3.03/0.79  % (23701)Memory used [KB]: 9083
% 3.03/0.79  % (23701)Time elapsed: 0.358 s
% 3.03/0.79  % (23701)------------------------------
% 3.03/0.79  % (23701)------------------------------
% 3.03/0.80  % (23690)Success in time 0.435 s
%------------------------------------------------------------------------------
