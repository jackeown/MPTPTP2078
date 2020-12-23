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
% DateTime   : Thu Dec  3 12:54:07 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 243 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  191 ( 720 expanded)
%              Number of equality atoms :   50 ( 144 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2683,plain,(
    $false ),
    inference(resolution,[],[f2598,f46])).

fof(f46,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

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

fof(f2598,plain,(
    ! [X10] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) ),
    inference(trivial_inequality_removal,[],[f2571])).

fof(f2571,plain,(
    ! [X10] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10) ) ),
    inference(superposition,[],[f71,f2553])).

fof(f2553,plain,(
    ! [X11] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11) ),
    inference(forward_demodulation,[],[f2552,f459])).

fof(f459,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f445,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f70,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f445,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f340,f98])).

fof(f340,plain,(
    ! [X0,X1] : k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(subsumption_resolution,[],[f339,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f339,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f2552,plain,(
    ! [X11] : k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11) ),
    inference(subsumption_resolution,[],[f2551,f106])).

fof(f106,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(superposition,[],[f69,f98])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2551,plain,(
    ! [X11] :
      ( ~ r1_tarski(k1_xboole_0,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11) ) ),
    inference(forward_demodulation,[],[f2550,f459])).

fof(f2550,plain,(
    ! [X11] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11) ) ),
    inference(subsumption_resolution,[],[f2549,f660])).

fof(f660,plain,(
    ! [X10,X9] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X9),X10),k1_relat_1(sK1)) ),
    inference(superposition,[],[f91,f551])).

fof(f551,plain,(
    ! [X0] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f78,f43])).

fof(f78,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(X3) = k2_xboole_0(k10_relat_1(X3,X4),k1_relat_1(X3)) ) ),
    inference(resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f91,plain,(
    ! [X4,X2,X3] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4)) ),
    inference(superposition,[],[f85,f77])).

fof(f77,plain,(
    ! [X2,X1] : k2_xboole_0(k6_subset_1(X1,X2),X1) = X1 ),
    inference(resolution,[],[f55,f69])).

fof(f85,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f64,f72])).

fof(f2549,plain,(
    ! [X11] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11))
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f2535,f43])).

fof(f2535,plain,(
    ! [X11] :
      ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11))
      | ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f258,f692])).

fof(f692,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ),
    inference(superposition,[],[f593,f384])).

fof(f384,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f383,f43])).

fof(f383,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f382,f44])).

fof(f382,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f593,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f592,f43])).

fof(f592,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f207,f44])).

fof(f207,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X2,k10_relat_1(X2,X3)),X3) ) ),
    inference(resolution,[],[f56,f70])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
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

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f51])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:17:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (27198)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (27193)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (27212)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (27212)Refutation not found, incomplete strategy% (27212)------------------------------
% 0.22/0.51  % (27212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27212)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27212)Memory used [KB]: 1663
% 0.22/0.51  % (27212)Time elapsed: 0.003 s
% 0.22/0.51  % (27212)------------------------------
% 0.22/0.51  % (27212)------------------------------
% 0.22/0.51  % (27193)Refutation not found, incomplete strategy% (27193)------------------------------
% 0.22/0.51  % (27193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27193)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27193)Memory used [KB]: 10746
% 0.22/0.51  % (27193)Time elapsed: 0.067 s
% 0.22/0.51  % (27193)------------------------------
% 0.22/0.51  % (27193)------------------------------
% 0.22/0.51  % (27188)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.52  % (27189)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (27196)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.22/0.53  % (27185)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (27183)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.53  % (27184)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.53  % (27186)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.53  % (27187)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.53  % (27203)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.53  % (27210)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.35/0.54  % (27207)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.54  % (27190)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.54  % (27204)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.54  % (27211)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.54  % (27201)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.35/0.54  % (27211)Refutation not found, incomplete strategy% (27211)------------------------------
% 1.35/0.54  % (27211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (27211)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (27211)Memory used [KB]: 10746
% 1.35/0.54  % (27211)Time elapsed: 0.132 s
% 1.35/0.54  % (27211)------------------------------
% 1.35/0.54  % (27211)------------------------------
% 1.35/0.54  % (27199)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.54  % (27209)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (27205)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.55  % (27197)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.35/0.55  % (27206)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.35/0.55  % (27208)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.55  % (27194)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.35/0.56  % (27191)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.35/0.56  % (27192)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.56  % (27195)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.35/0.56  % (27202)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.35/0.56  % (27199)Refutation not found, incomplete strategy% (27199)------------------------------
% 1.35/0.56  % (27199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (27199)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (27199)Memory used [KB]: 10618
% 1.35/0.56  % (27199)Time elapsed: 0.131 s
% 1.35/0.56  % (27199)------------------------------
% 1.35/0.56  % (27199)------------------------------
% 1.35/0.57  % (27200)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.35/0.62  % (27219)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.35/0.62  % (27220)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.97/0.65  % (27186)Refutation not found, incomplete strategy% (27186)------------------------------
% 1.97/0.65  % (27186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (27186)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.65  
% 1.97/0.65  % (27186)Memory used [KB]: 6140
% 1.97/0.65  % (27186)Time elapsed: 0.224 s
% 1.97/0.65  % (27186)------------------------------
% 1.97/0.65  % (27186)------------------------------
% 1.97/0.66  % (27189)Refutation found. Thanks to Tanya!
% 1.97/0.66  % SZS status Theorem for theBenchmark
% 1.97/0.66  % SZS output start Proof for theBenchmark
% 1.97/0.66  fof(f2683,plain,(
% 1.97/0.66    $false),
% 1.97/0.66    inference(resolution,[],[f2598,f46])).
% 1.97/0.66  fof(f46,plain,(
% 1.97/0.66    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.97/0.66    inference(cnf_transformation,[],[f39])).
% 1.97/0.66  fof(f39,plain,(
% 1.97/0.66    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.97/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f38])).
% 1.97/0.66  fof(f38,plain,(
% 1.97/0.66    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.97/0.66    introduced(choice_axiom,[])).
% 1.97/0.66  fof(f21,plain,(
% 1.97/0.66    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.97/0.66    inference(flattening,[],[f20])).
% 1.97/0.66  fof(f20,plain,(
% 1.97/0.66    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.97/0.66    inference(ennf_transformation,[],[f19])).
% 1.97/0.66  fof(f19,negated_conjecture,(
% 1.97/0.66    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.97/0.66    inference(negated_conjecture,[],[f18])).
% 1.97/0.66  fof(f18,conjecture,(
% 1.97/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.97/0.66  fof(f2598,plain,(
% 1.97/0.66    ( ! [X10] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) )),
% 1.97/0.66    inference(trivial_inequality_removal,[],[f2571])).
% 1.97/0.66  fof(f2571,plain,(
% 1.97/0.66    ( ! [X10] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10)) )),
% 1.97/0.66    inference(superposition,[],[f71,f2553])).
% 1.97/0.66  fof(f2553,plain,(
% 1.97/0.66    ( ! [X11] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) )),
% 1.97/0.66    inference(forward_demodulation,[],[f2552,f459])).
% 1.97/0.66  fof(f459,plain,(
% 1.97/0.66    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.97/0.66    inference(forward_demodulation,[],[f445,f98])).
% 1.97/0.66  fof(f98,plain,(
% 1.97/0.66    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.97/0.66    inference(resolution,[],[f70,f72])).
% 1.97/0.66  fof(f72,plain,(
% 1.97/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.97/0.66    inference(equality_resolution,[],[f58])).
% 1.97/0.66  fof(f58,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.97/0.66    inference(cnf_transformation,[],[f41])).
% 1.97/0.66  fof(f41,plain,(
% 1.97/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.66    inference(flattening,[],[f40])).
% 1.97/0.66  fof(f40,plain,(
% 1.97/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.66    inference(nnf_transformation,[],[f1])).
% 1.97/0.66  fof(f1,axiom,(
% 1.97/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.97/0.66  fof(f70,plain,(
% 1.97/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.97/0.66    inference(definition_unfolding,[],[f61,f51])).
% 1.97/0.66  fof(f51,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f8])).
% 1.97/0.66  fof(f8,axiom,(
% 1.97/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.97/0.66  fof(f61,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f42])).
% 1.97/0.66  fof(f42,plain,(
% 1.97/0.66    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.97/0.66    inference(nnf_transformation,[],[f2])).
% 1.97/0.66  fof(f2,axiom,(
% 1.97/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.97/0.66  fof(f445,plain,(
% 1.97/0.66    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 1.97/0.66    inference(superposition,[],[f340,f98])).
% 1.97/0.66  fof(f340,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))) )),
% 1.97/0.66    inference(subsumption_resolution,[],[f339,f43])).
% 1.97/0.66  fof(f43,plain,(
% 1.97/0.66    v1_relat_1(sK1)),
% 1.97/0.66    inference(cnf_transformation,[],[f39])).
% 1.97/0.66  fof(f339,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) | ~v1_relat_1(sK1)) )),
% 1.97/0.66    inference(resolution,[],[f65,f44])).
% 1.97/0.66  fof(f44,plain,(
% 1.97/0.66    v1_funct_1(sK1)),
% 1.97/0.66    inference(cnf_transformation,[],[f39])).
% 1.97/0.66  fof(f65,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f35])).
% 1.97/0.66  fof(f35,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.97/0.66    inference(flattening,[],[f34])).
% 1.97/0.66  fof(f34,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.97/0.66    inference(ennf_transformation,[],[f15])).
% 1.97/0.66  fof(f15,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.97/0.66  fof(f2552,plain,(
% 1.97/0.66    ( ! [X11] : (k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) )),
% 1.97/0.66    inference(subsumption_resolution,[],[f2551,f106])).
% 1.97/0.66  fof(f106,plain,(
% 1.97/0.66    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 1.97/0.66    inference(superposition,[],[f69,f98])).
% 1.97/0.66  fof(f69,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.97/0.66    inference(definition_unfolding,[],[f50,f51])).
% 1.97/0.66  fof(f50,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f5])).
% 1.97/0.66  fof(f5,axiom,(
% 1.97/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.97/0.66  fof(f2551,plain,(
% 1.97/0.66    ( ! [X11] : (~r1_tarski(k1_xboole_0,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) )),
% 1.97/0.66    inference(forward_demodulation,[],[f2550,f459])).
% 1.97/0.66  fof(f2550,plain,(
% 1.97/0.66    ( ! [X11] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) )),
% 1.97/0.66    inference(subsumption_resolution,[],[f2549,f660])).
% 1.97/0.66  fof(f660,plain,(
% 1.97/0.66    ( ! [X10,X9] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X9),X10),k1_relat_1(sK1))) )),
% 1.97/0.66    inference(superposition,[],[f91,f551])).
% 1.97/0.66  fof(f551,plain,(
% 1.97/0.66    ( ! [X0] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.97/0.66    inference(resolution,[],[f78,f43])).
% 1.97/0.66  fof(f78,plain,(
% 1.97/0.66    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_relat_1(X3) = k2_xboole_0(k10_relat_1(X3,X4),k1_relat_1(X3))) )),
% 1.97/0.66    inference(resolution,[],[f55,f52])).
% 1.97/0.66  fof(f52,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f23])).
% 1.97/0.66  fof(f23,plain,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.97/0.66    inference(ennf_transformation,[],[f9])).
% 1.97/0.66  fof(f9,axiom,(
% 1.97/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.97/0.66  fof(f55,plain,(
% 1.97/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.97/0.66    inference(cnf_transformation,[],[f27])).
% 1.97/0.66  fof(f27,plain,(
% 1.97/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.97/0.66    inference(ennf_transformation,[],[f4])).
% 1.97/0.66  fof(f4,axiom,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.97/0.66  fof(f91,plain,(
% 1.97/0.66    ( ! [X4,X2,X3] : (r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4))) )),
% 1.97/0.66    inference(superposition,[],[f85,f77])).
% 1.97/0.66  fof(f77,plain,(
% 1.97/0.66    ( ! [X2,X1] : (k2_xboole_0(k6_subset_1(X1,X2),X1) = X1) )),
% 1.97/0.66    inference(resolution,[],[f55,f69])).
% 1.97/0.66  fof(f85,plain,(
% 1.97/0.66    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 1.97/0.66    inference(resolution,[],[f81,f64])).
% 1.97/0.66  fof(f64,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f33])).
% 1.97/0.66  fof(f33,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.97/0.66    inference(ennf_transformation,[],[f3])).
% 1.97/0.66  fof(f3,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.97/0.66  fof(f81,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.97/0.66    inference(resolution,[],[f64,f72])).
% 1.97/0.66  fof(f2549,plain,(
% 1.97/0.66    ( ! [X11] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1))) )),
% 1.97/0.66    inference(subsumption_resolution,[],[f2535,f43])).
% 1.97/0.66  fof(f2535,plain,(
% 1.97/0.66    ( ! [X11] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11)) | ~v1_relat_1(sK1) | k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1))) )),
% 1.97/0.66    inference(superposition,[],[f258,f692])).
% 1.97/0.66  fof(f692,plain,(
% 1.97/0.66    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1))) )),
% 1.97/0.66    inference(superposition,[],[f593,f384])).
% 1.97/0.66  fof(f384,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.97/0.66    inference(subsumption_resolution,[],[f383,f43])).
% 1.97/0.66  fof(f383,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.97/0.66    inference(subsumption_resolution,[],[f382,f44])).
% 1.97/0.66  fof(f382,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.97/0.66    inference(resolution,[],[f66,f45])).
% 1.97/0.66  fof(f45,plain,(
% 1.97/0.66    v2_funct_1(sK1)),
% 1.97/0.66    inference(cnf_transformation,[],[f39])).
% 1.97/0.66  fof(f66,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f37])).
% 1.97/0.66  fof(f37,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.97/0.66    inference(flattening,[],[f36])).
% 1.97/0.66  fof(f36,plain,(
% 1.97/0.66    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.97/0.66    inference(ennf_transformation,[],[f14])).
% 1.97/0.66  fof(f14,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.97/0.66  fof(f593,plain,(
% 1.97/0.66    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.97/0.66    inference(subsumption_resolution,[],[f592,f43])).
% 1.97/0.66  fof(f592,plain,(
% 1.97/0.66    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.97/0.66    inference(resolution,[],[f207,f44])).
% 1.97/0.66  fof(f207,plain,(
% 1.97/0.66    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_xboole_0 = k6_subset_1(k9_relat_1(X2,k10_relat_1(X2,X3)),X3)) )),
% 1.97/0.66    inference(resolution,[],[f56,f70])).
% 1.97/0.66  fof(f56,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f29])).
% 1.97/0.66  fof(f29,plain,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.97/0.66    inference(flattening,[],[f28])).
% 1.97/0.66  fof(f28,plain,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.97/0.66    inference(ennf_transformation,[],[f16])).
% 1.97/0.66  fof(f16,axiom,(
% 1.97/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.97/0.66  fof(f258,plain,(
% 1.97/0.66    ( ! [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_relat_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) )),
% 1.97/0.66    inference(resolution,[],[f54,f59])).
% 1.97/0.66  fof(f59,plain,(
% 1.97/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f41])).
% 1.97/0.66  fof(f54,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f26])).
% 1.97/0.66  fof(f26,plain,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.97/0.66    inference(flattening,[],[f25])).
% 1.97/0.66  fof(f25,plain,(
% 1.97/0.66    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.97/0.66    inference(ennf_transformation,[],[f17])).
% 1.97/0.66  fof(f17,axiom,(
% 1.97/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.97/0.66  fof(f71,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(definition_unfolding,[],[f60,f51])).
% 1.97/0.66  fof(f60,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.97/0.66    inference(cnf_transformation,[],[f42])).
% 1.97/0.66  % SZS output end Proof for theBenchmark
% 1.97/0.66  % (27189)------------------------------
% 1.97/0.66  % (27189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (27189)Termination reason: Refutation
% 1.97/0.66  
% 1.97/0.66  % (27189)Memory used [KB]: 12409
% 1.97/0.66  % (27189)Time elapsed: 0.250 s
% 1.97/0.66  % (27189)------------------------------
% 1.97/0.66  % (27189)------------------------------
% 1.97/0.66  % (27182)Success in time 0.292 s
%------------------------------------------------------------------------------
