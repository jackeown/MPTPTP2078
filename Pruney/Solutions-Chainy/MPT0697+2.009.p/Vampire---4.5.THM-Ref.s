%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:07 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 211 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  183 ( 616 expanded)
%              Number of equality atoms :   42 ( 125 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f556,plain,(
    $false ),
    inference(resolution,[],[f519,f33])).

fof(f33,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f25])).

fof(f25,plain,
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

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f519,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(resolution,[],[f518,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f62,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f61,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f50,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f48,f51])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f35])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k6_subset_1(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(extensionality_resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f518,plain,(
    ! [X10] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0) ),
    inference(forward_demodulation,[],[f517,f117])).

fof(f117,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f112,f53])).

fof(f112,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f100,f53])).

fof(f100,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f99,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f517,plain,(
    ! [X10] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f516,f30])).

fof(f516,plain,(
    ! [X10] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f503,f253])).

fof(f253,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f49,f158])).

fof(f158,plain,(
    ! [X14,X15] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,X14),X15),k1_relat_1(sK1)) ),
    inference(resolution,[],[f59,f95])).

fof(f95,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f49,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f54,f30])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k6_subset_1(k10_relat_1(X1,X2),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X2),X1) ) ),
    inference(resolution,[],[f50,f48])).

fof(f503,plain,(
    ! [X10] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0))
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f37,f395])).

fof(f395,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    inference(superposition,[],[f390,f121])).

fof(f121,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f120,f30])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f119,f31])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f390,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f389,f30])).

fof(f389,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f80,f31])).

fof(f80,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5) ) ),
    inference(resolution,[],[f38,f48])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.55  % (8004)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (8027)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.56  % (8020)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.36/0.57  % (8007)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.57  % (8024)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.57  % (8006)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.57  % (8005)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.36/0.57  % (8011)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.57  % (8025)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.57  % (8018)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.58  % (8009)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.58  % (8017)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.58  % (8029)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.66/0.58  % (8008)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.66/0.58  % (8016)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.66/0.58  % (8022)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.58  % (8013)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.66/0.59  % (8013)Refutation not found, incomplete strategy% (8013)------------------------------
% 1.66/0.59  % (8013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (8013)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (8013)Memory used [KB]: 10618
% 1.66/0.59  % (8013)Time elapsed: 0.151 s
% 1.66/0.59  % (8013)------------------------------
% 1.66/0.59  % (8013)------------------------------
% 1.66/0.59  % (8015)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.66/0.59  % (8015)Refutation not found, incomplete strategy% (8015)------------------------------
% 1.66/0.59  % (8015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (8015)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (8015)Memory used [KB]: 10618
% 1.66/0.59  % (8015)Time elapsed: 0.172 s
% 1.66/0.59  % (8015)------------------------------
% 1.66/0.59  % (8015)------------------------------
% 1.66/0.59  % (8031)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.66/0.59  % (8023)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.66/0.59  % (8031)Refutation not found, incomplete strategy% (8031)------------------------------
% 1.66/0.59  % (8031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (8031)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (8031)Memory used [KB]: 10618
% 1.66/0.59  % (8031)Time elapsed: 0.148 s
% 1.66/0.59  % (8031)------------------------------
% 1.66/0.59  % (8031)------------------------------
% 1.66/0.59  % (8030)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.59  % (8028)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.60  % (8003)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.66/0.60  % (8009)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f556,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(resolution,[],[f519,f33])).
% 1.66/0.60  fof(f33,plain,(
% 1.66/0.60    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f26])).
% 1.66/0.60  fof(f26,plain,(
% 1.66/0.60    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f25])).
% 1.66/0.60  fof(f25,plain,(
% 1.66/0.60    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f14,plain,(
% 1.66/0.60    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.66/0.60    inference(flattening,[],[f13])).
% 1.66/0.60  fof(f13,plain,(
% 1.66/0.60    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.66/0.60    inference(ennf_transformation,[],[f12])).
% 1.66/0.60  fof(f12,negated_conjecture,(
% 1.66/0.60    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.66/0.60    inference(negated_conjecture,[],[f11])).
% 1.66/0.60  fof(f11,conjecture,(
% 1.66/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.66/0.60  fof(f519,plain,(
% 1.66/0.60    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.66/0.60    inference(resolution,[],[f518,f163])).
% 1.66/0.60  fof(f163,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f62,f69])).
% 1.66/0.60  fof(f69,plain,(
% 1.66/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.60    inference(resolution,[],[f61,f51])).
% 1.66/0.60  fof(f51,plain,(
% 1.66/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.60    inference(equality_resolution,[],[f40])).
% 1.66/0.60  fof(f40,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.60    inference(cnf_transformation,[],[f28])).
% 1.66/0.60  fof(f28,plain,(
% 1.66/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.60    inference(flattening,[],[f27])).
% 1.66/0.60  fof(f27,plain,(
% 1.66/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.60    inference(nnf_transformation,[],[f1])).
% 1.66/0.60  fof(f1,axiom,(
% 1.66/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.60  fof(f61,plain,(
% 1.66/0.60    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k1_xboole_0,X3)) )),
% 1.66/0.60    inference(superposition,[],[f50,f53])).
% 1.66/0.60  fof(f53,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.66/0.60    inference(resolution,[],[f48,f51])).
% 1.66/0.60  fof(f48,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f43,f35])).
% 1.66/0.60  fof(f35,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f5])).
% 1.66/0.60  fof(f5,axiom,(
% 1.66/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.66/0.60  fof(f43,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f29])).
% 1.66/0.60  fof(f29,plain,(
% 1.66/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.66/0.60    inference(nnf_transformation,[],[f2])).
% 1.66/0.60  fof(f2,axiom,(
% 1.66/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.66/0.60  fof(f50,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f44,f35])).
% 1.66/0.60  fof(f44,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f20])).
% 1.66/0.60  fof(f20,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f3])).
% 1.66/0.60  fof(f3,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.66/0.60  fof(f62,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_subset_1(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(extensionality_resolution,[],[f41,f49])).
% 1.66/0.60  fof(f49,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f42,f35])).
% 1.66/0.60  fof(f42,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.66/0.60    inference(cnf_transformation,[],[f29])).
% 1.66/0.60  fof(f41,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f28])).
% 1.66/0.60  fof(f518,plain,(
% 1.66/0.60    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f517,f117])).
% 1.66/0.60  fof(f117,plain,(
% 1.66/0.60    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.66/0.60    inference(forward_demodulation,[],[f112,f53])).
% 1.66/0.60  fof(f112,plain,(
% 1.66/0.60    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 1.66/0.60    inference(superposition,[],[f100,f53])).
% 1.66/0.60  fof(f100,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f99,f30])).
% 1.66/0.60  fof(f30,plain,(
% 1.66/0.60    v1_relat_1(sK1)),
% 1.66/0.60    inference(cnf_transformation,[],[f26])).
% 1.66/0.60  fof(f99,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.66/0.60    inference(resolution,[],[f45,f31])).
% 1.66/0.60  fof(f31,plain,(
% 1.66/0.60    v1_funct_1(sK1)),
% 1.66/0.60    inference(cnf_transformation,[],[f26])).
% 1.66/0.60  fof(f45,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f22])).
% 1.66/0.60  fof(f22,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.60    inference(flattening,[],[f21])).
% 1.66/0.60  fof(f21,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.66/0.60    inference(ennf_transformation,[],[f8])).
% 1.66/0.60  fof(f8,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.66/0.60  fof(f517,plain,(
% 1.66/0.60    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f516,f30])).
% 1.66/0.60  fof(f516,plain,(
% 1.66/0.60    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0)) | ~v1_relat_1(sK1)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f503,f253])).
% 1.66/0.60  fof(f253,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))) )),
% 1.66/0.60    inference(trivial_inequality_removal,[],[f246])).
% 1.66/0.60  fof(f246,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))) )),
% 1.66/0.60    inference(superposition,[],[f49,f158])).
% 1.66/0.60  fof(f158,plain,(
% 1.66/0.60    ( ! [X14,X15] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,X14),X15),k1_relat_1(sK1))) )),
% 1.66/0.60    inference(resolution,[],[f59,f95])).
% 1.66/0.60  fof(f95,plain,(
% 1.66/0.60    ( ! [X2] : (r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))) )),
% 1.66/0.60    inference(trivial_inequality_removal,[],[f94])).
% 1.66/0.60  fof(f94,plain,(
% 1.66/0.60    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))) )),
% 1.66/0.60    inference(superposition,[],[f49,f92])).
% 1.66/0.60  fof(f92,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.66/0.60    inference(resolution,[],[f54,f30])).
% 1.66/0.60  fof(f54,plain,(
% 1.66/0.60    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k6_subset_1(k10_relat_1(X1,X2),k1_relat_1(X1))) )),
% 1.66/0.60    inference(resolution,[],[f48,f36])).
% 1.66/0.60  fof(f36,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f15])).
% 1.66/0.60  fof(f15,plain,(
% 1.66/0.60    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f6])).
% 1.66/0.60  fof(f6,axiom,(
% 1.66/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.66/0.60  fof(f59,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X2),X1)) )),
% 1.66/0.60    inference(resolution,[],[f50,f48])).
% 1.66/0.60  fof(f503,plain,(
% 1.66/0.60    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.66/0.60    inference(superposition,[],[f37,f395])).
% 1.66/0.60  fof(f395,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) )),
% 1.66/0.60    inference(superposition,[],[f390,f121])).
% 1.66/0.60  fof(f121,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f120,f30])).
% 1.66/0.60  fof(f120,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f119,f31])).
% 1.66/0.60  fof(f119,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.66/0.60    inference(resolution,[],[f46,f32])).
% 1.66/0.60  fof(f32,plain,(
% 1.66/0.60    v2_funct_1(sK1)),
% 1.66/0.60    inference(cnf_transformation,[],[f26])).
% 1.66/0.60  fof(f46,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f24])).
% 1.66/0.60  fof(f24,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.60    inference(flattening,[],[f23])).
% 1.66/0.60  fof(f23,plain,(
% 1.66/0.60    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.66/0.60    inference(ennf_transformation,[],[f7])).
% 1.66/0.60  fof(f7,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.66/0.60  fof(f390,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f389,f30])).
% 1.66/0.60  fof(f389,plain,(
% 1.66/0.60    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.66/0.60    inference(resolution,[],[f80,f31])).
% 1.66/0.60  fof(f80,plain,(
% 1.66/0.60    ( ! [X4,X5] : (~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = k6_subset_1(k9_relat_1(X4,k10_relat_1(X4,X5)),X5)) )),
% 1.66/0.60    inference(resolution,[],[f38,f48])).
% 1.66/0.60  fof(f38,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f19])).
% 1.66/0.60  fof(f19,plain,(
% 1.66/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.66/0.60    inference(flattening,[],[f18])).
% 1.66/0.60  fof(f18,plain,(
% 1.66/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.66/0.60    inference(ennf_transformation,[],[f9])).
% 1.66/0.60  fof(f9,axiom,(
% 1.66/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.66/0.60  fof(f37,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f17,plain,(
% 1.66/0.60    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.66/0.60    inference(flattening,[],[f16])).
% 1.66/0.60  fof(f16,plain,(
% 1.66/0.60    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f10])).
% 1.66/0.60  fof(f10,axiom,(
% 1.66/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.66/0.60  % SZS output end Proof for theBenchmark
% 1.66/0.60  % (8009)------------------------------
% 1.66/0.60  % (8009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (8009)Termination reason: Refutation
% 1.66/0.60  
% 1.66/0.60  % (8009)Memory used [KB]: 11001
% 1.66/0.60  % (8009)Time elapsed: 0.121 s
% 1.66/0.60  % (8009)------------------------------
% 1.66/0.60  % (8009)------------------------------
% 1.66/0.61  % (8032)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.61  % (8032)Refutation not found, incomplete strategy% (8032)------------------------------
% 1.66/0.61  % (8032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (8032)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (8032)Memory used [KB]: 1663
% 1.66/0.61  % (8032)Time elapsed: 0.001 s
% 1.66/0.61  % (8032)------------------------------
% 1.66/0.61  % (8032)------------------------------
% 1.66/0.61  % (8026)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.61  % (8010)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.61  % (8021)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.66/0.62  % (8019)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.62  % (8019)Refutation not found, incomplete strategy% (8019)------------------------------
% 1.66/0.62  % (8019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (8019)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.62  
% 1.66/0.62  % (8019)Memory used [KB]: 10618
% 1.66/0.62  % (8019)Time elapsed: 0.199 s
% 1.66/0.62  % (8019)------------------------------
% 1.66/0.62  % (8019)------------------------------
% 1.66/0.62  % (8012)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.66/0.63  % (8014)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.66/0.63  % (7998)Success in time 0.265 s
%------------------------------------------------------------------------------
