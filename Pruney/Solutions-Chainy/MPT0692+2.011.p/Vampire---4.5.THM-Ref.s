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
% DateTime   : Thu Dec  3 12:53:57 EST 2020

% Result     : Theorem 4.48s
% Output     : Refutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 828 expanded)
%              Number of leaves         :   13 ( 215 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 (2667 expanded)
%              Number of equality atoms :   54 ( 675 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9852,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9851,f482])).

fof(f482,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f422,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f422,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f52,f401,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f401,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,X3)) ),
    inference(superposition,[],[f52,f137])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f100,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f40])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f100,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k1_xboole_0,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f52,f95,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f95,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(superposition,[],[f52,f76])).

fof(f76,plain,(
    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f53])).

fof(f36,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f9851,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f9850,f1632])).

fof(f1632,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1603,f1612])).

fof(f1612,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f34,f72,f1603,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f52,f36,f51])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f1603,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(sK0,sK0)) ),
    inference(superposition,[],[f1600,f66])).

fof(f66,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f1600,plain,(
    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f1580,f1584])).

fof(f1584,plain,(
    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1583,f173])).

fof(f173,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k10_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f67,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f34,f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f1583,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k10_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f108,f46])).

fof(f108,plain,(
    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f34,f80,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f80,plain,(
    r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f75,f63])).

fof(f63,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f75,plain,(
    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f34,f36,f49])).

fof(f1580,plain,(
    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f108,f53])).

fof(f9850,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f9849,f1612])).

fof(f9849,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f9848,f9331])).

fof(f9331,plain,(
    ! [X2] : k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k10_relat_1(sK1,k6_subset_1(X2,sK0)) ),
    inference(forward_demodulation,[],[f9281,f66])).

fof(f9281,plain,(
    ! [X2] : k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f66,f1584])).

fof(f9848,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f482,f1442,f46])).

fof(f1442,plain,(
    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f34,f72,f231,f42])).

fof(f231,plain,(
    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f176,f54])).

fof(f176,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f37,f67,f46])).

fof(f37,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (14687)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (14709)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (14700)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (14690)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (14710)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (14694)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.24/0.53  % (14686)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.53  % (14681)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.53  % (14693)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.24/0.53  % (14683)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.54  % (14682)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.54  % (14708)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.24/0.54  % (14695)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.45/0.55  % (14705)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.45/0.55  % (14704)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.45/0.55  % (14692)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.45/0.55  % (14691)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.45/0.55  % (14688)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.45/0.55  % (14697)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.45/0.55  % (14689)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.45/0.56  % (14702)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.45/0.56  % (14696)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.45/0.56  % (14701)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.56  % (14703)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.45/0.56  % (14685)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.45/0.56  % (14684)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.45/0.57  % (14707)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.45/0.57  % (14706)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.45/0.57  % (14699)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.45/0.57  % (14698)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 3.48/0.81  % (14705)Time limit reached!
% 3.48/0.81  % (14705)------------------------------
% 3.48/0.81  % (14705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.81  % (14683)Time limit reached!
% 3.48/0.81  % (14683)------------------------------
% 3.48/0.81  % (14683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.82  % (14683)Termination reason: Time limit
% 3.48/0.82  
% 3.48/0.82  % (14683)Memory used [KB]: 6524
% 3.48/0.82  % (14683)Time elapsed: 0.408 s
% 3.48/0.82  % (14683)------------------------------
% 3.48/0.82  % (14683)------------------------------
% 3.48/0.82  % (14705)Termination reason: Time limit
% 3.48/0.82  
% 3.48/0.82  % (14705)Memory used [KB]: 12665
% 3.48/0.82  % (14705)Time elapsed: 0.412 s
% 3.48/0.82  % (14705)------------------------------
% 3.48/0.82  % (14705)------------------------------
% 4.48/0.94  % (14687)Time limit reached!
% 4.48/0.94  % (14687)------------------------------
% 4.48/0.94  % (14687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.94  % (14695)Time limit reached!
% 4.48/0.94  % (14695)------------------------------
% 4.48/0.94  % (14695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.95  % (14695)Termination reason: Time limit
% 4.48/0.95  % (14687)Termination reason: Time limit
% 4.48/0.95  
% 4.48/0.95  % (14687)Memory used [KB]: 17142
% 4.48/0.95  % (14687)Time elapsed: 0.513 s
% 4.48/0.95  % (14687)------------------------------
% 4.48/0.95  % (14687)------------------------------
% 4.48/0.95  
% 4.48/0.95  % (14695)Memory used [KB]: 5245
% 4.48/0.95  % (14695)Time elapsed: 0.511 s
% 4.48/0.95  % (14695)------------------------------
% 4.48/0.95  % (14695)------------------------------
% 4.48/0.97  % (14711)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.48/0.99  % (14692)Refutation found. Thanks to Tanya!
% 4.48/0.99  % SZS status Theorem for theBenchmark
% 4.48/0.99  % SZS output start Proof for theBenchmark
% 4.48/0.99  fof(f9852,plain,(
% 4.48/0.99    $false),
% 4.48/0.99    inference(subsumption_resolution,[],[f9851,f482])).
% 4.48/0.99  fof(f482,plain,(
% 4.48/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f422,f54])).
% 4.48/0.99  fof(f54,plain,(
% 4.48/0.99    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 4.48/0.99    inference(definition_unfolding,[],[f47,f40])).
% 4.48/0.99  fof(f40,plain,(
% 4.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f5])).
% 4.48/0.99  fof(f5,axiom,(
% 4.48/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 4.48/0.99  fof(f47,plain,(
% 4.48/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.48/0.99    inference(cnf_transformation,[],[f33])).
% 4.48/0.99  fof(f33,plain,(
% 4.48/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.48/0.99    inference(nnf_transformation,[],[f2])).
% 4.48/0.99  fof(f2,axiom,(
% 4.48/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.48/0.99  fof(f422,plain,(
% 4.48/0.99    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f52,f401,f46])).
% 4.48/0.99  fof(f46,plain,(
% 4.48/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f32])).
% 4.48/0.99  fof(f32,plain,(
% 4.48/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.48/0.99    inference(flattening,[],[f31])).
% 4.48/0.99  fof(f31,plain,(
% 4.48/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.48/0.99    inference(nnf_transformation,[],[f1])).
% 4.48/0.99  fof(f1,axiom,(
% 4.48/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.48/0.99  fof(f401,plain,(
% 4.48/0.99    ( ! [X3] : (r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,X3))) )),
% 4.48/0.99    inference(superposition,[],[f52,f137])).
% 4.48/0.99  fof(f137,plain,(
% 4.48/0.99    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k1_xboole_0,X0),sK0)) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f100,f53])).
% 4.48/0.99  fof(f53,plain,(
% 4.48/0.99    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 4.48/0.99    inference(definition_unfolding,[],[f48,f40])).
% 4.48/0.99  fof(f48,plain,(
% 4.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f33])).
% 4.48/0.99  fof(f100,plain,(
% 4.48/0.99    ( ! [X0] : (r1_tarski(k6_subset_1(k1_xboole_0,X0),sK0)) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f52,f95,f51])).
% 4.48/0.99  fof(f51,plain,(
% 4.48/0.99    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f28])).
% 4.48/0.99  fof(f28,plain,(
% 4.48/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.48/0.99    inference(flattening,[],[f27])).
% 4.48/0.99  fof(f27,plain,(
% 4.48/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.48/0.99    inference(ennf_transformation,[],[f3])).
% 4.48/0.99  fof(f3,axiom,(
% 4.48/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.48/0.99  fof(f95,plain,(
% 4.48/0.99    r1_tarski(k1_xboole_0,sK0)),
% 4.48/0.99    inference(superposition,[],[f52,f76])).
% 4.48/0.99  fof(f76,plain,(
% 4.48/0.99    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f36,f53])).
% 4.48/0.99  fof(f36,plain,(
% 4.48/0.99    r1_tarski(sK0,k2_relat_1(sK1))),
% 4.48/0.99    inference(cnf_transformation,[],[f30])).
% 4.48/0.99  fof(f30,plain,(
% 4.48/0.99    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 4.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29])).
% 4.48/0.99  fof(f29,plain,(
% 4.48/0.99    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 4.48/0.99    introduced(choice_axiom,[])).
% 4.48/0.99  fof(f15,plain,(
% 4.48/0.99    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.48/0.99    inference(flattening,[],[f14])).
% 4.48/0.99  fof(f14,plain,(
% 4.48/0.99    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.48/0.99    inference(ennf_transformation,[],[f13])).
% 4.48/0.99  fof(f13,negated_conjecture,(
% 4.48/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 4.48/0.99    inference(negated_conjecture,[],[f12])).
% 4.48/0.99  fof(f12,conjecture,(
% 4.48/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 4.48/0.99  fof(f52,plain,(
% 4.48/0.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 4.48/0.99    inference(definition_unfolding,[],[f39,f40])).
% 4.48/0.99  fof(f39,plain,(
% 4.48/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f4])).
% 4.48/0.99  fof(f4,axiom,(
% 4.48/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.48/0.99  fof(f9851,plain,(
% 4.48/0.99    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 4.48/0.99    inference(forward_demodulation,[],[f9850,f1632])).
% 4.48/0.99  fof(f1632,plain,(
% 4.48/0.99    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 4.48/0.99    inference(backward_demodulation,[],[f1603,f1612])).
% 4.48/0.99  fof(f1612,plain,(
% 4.48/0.99    k1_xboole_0 = k6_subset_1(sK0,sK0)),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f72,f1603,f42])).
% 4.48/0.99  fof(f42,plain,(
% 4.48/0.99    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f20])).
% 4.48/0.99  fof(f20,plain,(
% 4.48/0.99    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 4.48/0.99    inference(flattening,[],[f19])).
% 4.48/0.99  fof(f19,plain,(
% 4.48/0.99    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 4.48/0.99    inference(ennf_transformation,[],[f7])).
% 4.48/0.99  fof(f7,axiom,(
% 4.48/0.99    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 4.48/0.99  fof(f72,plain,(
% 4.48/0.99    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1))) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f52,f36,f51])).
% 4.48/0.99  fof(f34,plain,(
% 4.48/0.99    v1_relat_1(sK1)),
% 4.48/0.99    inference(cnf_transformation,[],[f30])).
% 4.48/0.99  fof(f1603,plain,(
% 4.48/0.99    k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(sK0,sK0))),
% 4.48/0.99    inference(superposition,[],[f1600,f66])).
% 4.48/0.99  fof(f66,plain,(
% 4.48/0.99    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f35,f50])).
% 4.48/0.99  fof(f50,plain,(
% 4.48/0.99    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f26])).
% 4.48/0.99  fof(f26,plain,(
% 4.48/0.99    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.48/0.99    inference(flattening,[],[f25])).
% 4.48/0.99  fof(f25,plain,(
% 4.48/0.99    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.48/0.99    inference(ennf_transformation,[],[f9])).
% 4.48/0.99  fof(f9,axiom,(
% 4.48/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 4.48/0.99  fof(f35,plain,(
% 4.48/0.99    v1_funct_1(sK1)),
% 4.48/0.99    inference(cnf_transformation,[],[f30])).
% 4.48/0.99  fof(f1600,plain,(
% 4.48/0.99    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,sK0))),
% 4.48/0.99    inference(backward_demodulation,[],[f1580,f1584])).
% 4.48/0.99  fof(f1584,plain,(
% 4.48/0.99    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 4.48/0.99    inference(subsumption_resolution,[],[f1583,f173])).
% 4.48/0.99  fof(f173,plain,(
% 4.48/0.99    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k10_relat_1(sK1,X0))) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f67,f49])).
% 4.48/0.99  fof(f49,plain,(
% 4.48/0.99    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f24])).
% 4.48/0.99  fof(f24,plain,(
% 4.48/0.99    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 4.48/0.99    inference(flattening,[],[f23])).
% 4.48/0.99  fof(f23,plain,(
% 4.48/0.99    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 4.48/0.99    inference(ennf_transformation,[],[f8])).
% 4.48/0.99  fof(f8,axiom,(
% 4.48/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 4.48/0.99  fof(f67,plain,(
% 4.48/0.99    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f35,f43])).
% 4.48/0.99  fof(f43,plain,(
% 4.48/0.99    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f22])).
% 4.48/0.99  fof(f22,plain,(
% 4.48/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.48/0.99    inference(flattening,[],[f21])).
% 4.48/0.99  fof(f21,plain,(
% 4.48/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.48/0.99    inference(ennf_transformation,[],[f10])).
% 4.48/0.99  fof(f10,axiom,(
% 4.48/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 4.48/0.99  fof(f1583,plain,(
% 4.48/0.99    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k10_relat_1(sK1,sK0))),
% 4.48/0.99    inference(resolution,[],[f108,f46])).
% 4.48/0.99  fof(f108,plain,(
% 4.48/0.99    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f80,f41])).
% 4.48/0.99  fof(f41,plain,(
% 4.48/0.99    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 4.48/0.99    inference(cnf_transformation,[],[f18])).
% 4.48/0.99  fof(f18,plain,(
% 4.48/0.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.48/0.99    inference(flattening,[],[f17])).
% 4.48/0.99  fof(f17,plain,(
% 4.48/0.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.48/0.99    inference(ennf_transformation,[],[f11])).
% 4.48/0.99  fof(f11,axiom,(
% 4.48/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 4.48/0.99  fof(f80,plain,(
% 4.48/0.99    r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 4.48/0.99    inference(forward_demodulation,[],[f75,f63])).
% 4.48/0.99  fof(f63,plain,(
% 4.48/0.99    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f38])).
% 4.48/0.99  fof(f38,plain,(
% 4.48/0.99    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 4.48/0.99    inference(cnf_transformation,[],[f16])).
% 4.48/0.99  fof(f16,plain,(
% 4.48/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 4.48/0.99    inference(ennf_transformation,[],[f6])).
% 4.48/0.99  fof(f6,axiom,(
% 4.48/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 4.48/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 4.48/0.99  fof(f75,plain,(
% 4.48/0.99    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f36,f49])).
% 4.48/0.99  fof(f1580,plain,(
% 4.48/0.99    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f108,f53])).
% 4.48/0.99  fof(f9850,plain,(
% 4.48/0.99    ~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k1_xboole_0)),
% 4.48/0.99    inference(forward_demodulation,[],[f9849,f1612])).
% 4.48/0.99  fof(f9849,plain,(
% 4.48/0.99    ~r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,sK0)),k1_xboole_0)),
% 4.48/0.99    inference(forward_demodulation,[],[f9848,f9331])).
% 4.48/0.99  fof(f9331,plain,(
% 4.48/0.99    ( ! [X2] : (k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k10_relat_1(sK1,k6_subset_1(X2,sK0))) )),
% 4.48/0.99    inference(forward_demodulation,[],[f9281,f66])).
% 4.48/0.99  fof(f9281,plain,(
% 4.48/0.99    ( ! [X2] : (k10_relat_1(sK1,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,sK0))) )),
% 4.48/0.99    inference(superposition,[],[f66,f1584])).
% 4.48/0.99  fof(f9848,plain,(
% 4.48/0.99    ~r1_tarski(k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k1_xboole_0)),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f482,f1442,f46])).
% 4.48/0.99  fof(f1442,plain,(
% 4.48/0.99    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f34,f72,f231,f42])).
% 4.48/0.99  fof(f231,plain,(
% 4.48/0.99    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f176,f54])).
% 4.48/0.99  fof(f176,plain,(
% 4.48/0.99    ~r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 4.48/0.99    inference(unit_resulting_resolution,[],[f37,f67,f46])).
% 4.48/0.99  fof(f37,plain,(
% 4.48/0.99    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 4.48/0.99    inference(cnf_transformation,[],[f30])).
% 4.48/0.99  % SZS output end Proof for theBenchmark
% 4.48/0.99  % (14692)------------------------------
% 4.48/0.99  % (14692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.99  % (14692)Termination reason: Refutation
% 4.48/0.99  
% 4.48/0.99  % (14692)Memory used [KB]: 8955
% 4.48/0.99  % (14692)Time elapsed: 0.580 s
% 4.48/0.99  % (14692)------------------------------
% 4.48/0.99  % (14692)------------------------------
% 4.87/1.00  % (14712)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.87/1.01  % (14688)Time limit reached!
% 4.87/1.01  % (14688)------------------------------
% 4.87/1.01  % (14688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.01  % (14688)Termination reason: Time limit
% 4.87/1.01  % (14688)Termination phase: Saturation
% 4.87/1.01  
% 4.87/1.01  % (14688)Memory used [KB]: 6268
% 4.87/1.01  % (14688)Time elapsed: 0.600 s
% 4.87/1.01  % (14688)------------------------------
% 4.87/1.01  % (14688)------------------------------
% 4.87/1.01  % (14680)Success in time 0.648 s
%------------------------------------------------------------------------------
