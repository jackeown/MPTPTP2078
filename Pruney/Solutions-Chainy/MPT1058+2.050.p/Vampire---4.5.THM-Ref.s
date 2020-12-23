%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:24 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 173 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  195 ( 402 expanded)
%              Number of equality atoms :   43 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f436,f481])).

fof(f481,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f425,f72])).

fof(f72,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f425,plain,(
    ! [X6,X7] : r1_tarski(k10_relat_1(k7_relat_1(sK0,X7),X6),k10_relat_1(sK0,X6)) ),
    inference(superposition,[],[f58,f405])).

fof(f405,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
    inference(resolution,[],[f288,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k10_relat_1(k6_relat_1(k10_relat_1(X2,X1)),X0) ) ),
    inference(backward_demodulation,[],[f54,f273])).

fof(f273,plain,(
    ! [X6,X5] : k1_setfam_1(k2_tarski(X5,X6)) = k10_relat_1(k6_relat_1(X6),X5) ),
    inference(backward_demodulation,[],[f101,f250])).

fof(f250,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f114,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f114,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f112,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f112,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f101,plain,(
    ! [X6,X5] : k1_setfam_1(k2_tarski(X5,X6)) = k1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X5))) ),
    inference(superposition,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f436,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f420,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_1
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f420,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f322,f405])).

fof(f322,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    inference(subsumption_resolution,[],[f321,f37])).

fof(f37,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f321,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f312,f36])).

fof(f312,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f184,f289])).

fof(f289,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(superposition,[],[f273,f52])).

fof(f52,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f184,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f183,f44])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
      | ~ r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
      | ~ r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f92,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f92,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(sK0,sK2))),sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f85,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f85,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k10_relat_1(sK0,sK2))
      | r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f74,plain,
    ( ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f60,f66,f70])).

fof(f60,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) ),
    inference(extensionality_resolution,[],[f48,f35])).

fof(f35,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (5000)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.61/0.59  % (4996)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.61/0.59  % (4993)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.61/0.59  % (4991)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.61/0.59  % (4994)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.61/0.60  % (4992)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.61/0.60  % (5014)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.61/0.61  % (4995)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.61/0.61  % (5006)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.61/0.61  % (4992)Refutation not found, incomplete strategy% (4992)------------------------------
% 1.61/0.61  % (4992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.61  % (4992)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.61  
% 1.61/0.61  % (4992)Memory used [KB]: 1663
% 1.61/0.61  % (4992)Time elapsed: 0.137 s
% 1.61/0.61  % (4992)------------------------------
% 1.61/0.61  % (4992)------------------------------
% 1.61/0.61  % (5007)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.61/0.61  % (5018)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.61/0.62  % (5005)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.61/0.62  % (5016)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.61/0.62  % (5003)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.61/0.62  % (5004)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.61/0.62  % (4999)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.61/0.62  % (5020)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.61/0.62  % (5017)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.61/0.62  % (5008)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.61/0.63  % (5009)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.61/0.63  % (4997)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.63  % (5002)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.61/0.63  % (5021)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.61/0.63  % (5011)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.61/0.63  % (4998)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.61/0.64  % (5010)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.61/0.64  % (5012)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.61/0.64  % (5015)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.61/0.64  % (5001)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.14/0.66  % (4997)Refutation found. Thanks to Tanya!
% 2.14/0.66  % SZS status Theorem for theBenchmark
% 2.14/0.66  % SZS output start Proof for theBenchmark
% 2.14/0.66  fof(f482,plain,(
% 2.14/0.66    $false),
% 2.14/0.66    inference(avatar_sat_refutation,[],[f74,f436,f481])).
% 2.14/0.66  fof(f481,plain,(
% 2.14/0.66    spl3_2),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f475])).
% 2.14/0.66  fof(f475,plain,(
% 2.14/0.66    $false | spl3_2),
% 2.14/0.66    inference(resolution,[],[f425,f72])).
% 2.14/0.66  fof(f72,plain,(
% 2.14/0.66    ~r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) | spl3_2),
% 2.14/0.66    inference(avatar_component_clause,[],[f70])).
% 2.14/0.66  fof(f70,plain,(
% 2.14/0.66    spl3_2 <=> r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.14/0.66  fof(f425,plain,(
% 2.14/0.66    ( ! [X6,X7] : (r1_tarski(k10_relat_1(k7_relat_1(sK0,X7),X6),k10_relat_1(sK0,X6))) )),
% 2.14/0.66    inference(superposition,[],[f58,f405])).
% 2.14/0.66  fof(f405,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0)) )),
% 2.14/0.66    inference(resolution,[],[f288,f32])).
% 2.14/0.66  fof(f32,plain,(
% 2.14/0.66    v1_relat_1(sK0)),
% 2.14/0.66    inference(cnf_transformation,[],[f29])).
% 2.14/0.66  fof(f29,plain,(
% 2.14/0.66    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.14/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f28,f27])).
% 2.14/0.66  fof(f27,plain,(
% 2.14/0.66    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f28,plain,(
% 2.14/0.66    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 2.14/0.66    introduced(choice_axiom,[])).
% 2.14/0.66  fof(f17,plain,(
% 2.14/0.66    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f16])).
% 2.14/0.66  fof(f16,plain,(
% 2.14/0.66    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f14])).
% 2.14/0.66  fof(f14,negated_conjecture,(
% 2.14/0.66    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.14/0.66    inference(negated_conjecture,[],[f13])).
% 2.14/0.66  fof(f13,conjecture,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 2.14/0.66  fof(f288,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k10_relat_1(k6_relat_1(k10_relat_1(X2,X1)),X0)) )),
% 2.14/0.66    inference(backward_demodulation,[],[f54,f273])).
% 2.14/0.66  fof(f273,plain,(
% 2.14/0.66    ( ! [X6,X5] : (k1_setfam_1(k2_tarski(X5,X6)) = k10_relat_1(k6_relat_1(X6),X5)) )),
% 2.14/0.66    inference(backward_demodulation,[],[f101,f250])).
% 2.14/0.66  fof(f250,plain,(
% 2.14/0.66    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 2.14/0.66    inference(resolution,[],[f114,f36])).
% 2.14/0.66  fof(f36,plain,(
% 2.14/0.66    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.14/0.66    inference(cnf_transformation,[],[f8])).
% 2.14/0.66  fof(f8,axiom,(
% 2.14/0.66    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.14/0.66  fof(f114,plain,(
% 2.14/0.66    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) )),
% 2.14/0.66    inference(forward_demodulation,[],[f112,f38])).
% 2.14/0.66  fof(f38,plain,(
% 2.14/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.14/0.66    inference(cnf_transformation,[],[f7])).
% 2.14/0.66  fof(f7,axiom,(
% 2.14/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.14/0.66  fof(f112,plain,(
% 2.14/0.66    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(resolution,[],[f40,f36])).
% 2.14/0.66  fof(f40,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f18])).
% 2.14/0.66  fof(f18,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f6])).
% 2.14/0.66  fof(f6,axiom,(
% 2.14/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 2.14/0.66  fof(f101,plain,(
% 2.14/0.66    ( ! [X6,X5] : (k1_setfam_1(k2_tarski(X5,X6)) = k1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)))) )),
% 2.14/0.66    inference(superposition,[],[f38,f53])).
% 2.14/0.66  fof(f53,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.14/0.66    inference(definition_unfolding,[],[f43,f42])).
% 2.14/0.66  fof(f42,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f4])).
% 2.14/0.66  fof(f4,axiom,(
% 2.14/0.66    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.14/0.66  fof(f43,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 2.14/0.66    inference(cnf_transformation,[],[f12])).
% 2.14/0.66  fof(f12,axiom,(
% 2.14/0.66    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 2.14/0.66  fof(f54,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 2.14/0.66    inference(definition_unfolding,[],[f49,f42])).
% 2.14/0.66  fof(f49,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f22])).
% 2.14/0.66  fof(f22,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.14/0.66    inference(ennf_transformation,[],[f9])).
% 2.14/0.66  fof(f9,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.14/0.66  fof(f58,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f57,f36])).
% 2.14/0.66  fof(f57,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.14/0.66    inference(superposition,[],[f44,f38])).
% 2.14/0.66  fof(f44,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f19])).
% 2.14/0.66  fof(f19,plain,(
% 2.14/0.66    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f5])).
% 2.14/0.66  fof(f5,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.14/0.66  fof(f436,plain,(
% 2.14/0.66    spl3_1),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f435])).
% 2.14/0.66  fof(f435,plain,(
% 2.14/0.66    $false | spl3_1),
% 2.14/0.66    inference(subsumption_resolution,[],[f420,f68])).
% 2.14/0.66  fof(f68,plain,(
% 2.14/0.66    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | spl3_1),
% 2.14/0.66    inference(avatar_component_clause,[],[f66])).
% 2.14/0.66  fof(f66,plain,(
% 2.14/0.66    spl3_1 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.14/0.66  fof(f420,plain,(
% 2.14/0.66    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))),
% 2.14/0.66    inference(backward_demodulation,[],[f322,f405])).
% 2.14/0.66  fof(f322,plain,(
% 2.14/0.66    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 2.14/0.66    inference(subsumption_resolution,[],[f321,f37])).
% 2.14/0.66  fof(f37,plain,(
% 2.14/0.66    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.14/0.66    inference(cnf_transformation,[],[f8])).
% 2.14/0.66  fof(f321,plain,(
% 2.14/0.66    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 2.14/0.66    inference(subsumption_resolution,[],[f312,f36])).
% 2.14/0.66  fof(f312,plain,(
% 2.14/0.66    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 2.14/0.66    inference(superposition,[],[f184,f289])).
% 2.14/0.66  fof(f289,plain,(
% 2.14/0.66    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.14/0.66    inference(superposition,[],[f273,f52])).
% 2.14/0.66  fof(f52,plain,(
% 2.14/0.66    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.14/0.66    inference(definition_unfolding,[],[f41,f42])).
% 2.14/0.66  fof(f41,plain,(
% 2.14/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.14/0.66    inference(cnf_transformation,[],[f15])).
% 2.14/0.66  fof(f15,plain,(
% 2.14/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.14/0.66    inference(rectify,[],[f1])).
% 2.14/0.66  fof(f1,axiom,(
% 2.14/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.14/0.66  fof(f184,plain,(
% 2.14/0.66    ( ! [X0] : (r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 2.14/0.66    inference(subsumption_resolution,[],[f183,f44])).
% 2.14/0.66  fof(f183,plain,(
% 2.14/0.66    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0))) )),
% 2.14/0.66    inference(duplicate_literal_removal,[],[f179])).
% 2.14/0.66  fof(f179,plain,(
% 2.14/0.66    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(resolution,[],[f92,f50])).
% 2.14/0.66  fof(f50,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f24])).
% 2.14/0.66  fof(f24,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.14/0.66    inference(flattening,[],[f23])).
% 2.14/0.66  fof(f23,plain,(
% 2.14/0.66    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.14/0.66    inference(ennf_transformation,[],[f11])).
% 2.14/0.66  fof(f11,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 2.14/0.66  fof(f92,plain,(
% 2.14/0.66    ( ! [X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(sK0,sK2))),sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(resolution,[],[f85,f45])).
% 2.14/0.66  fof(f45,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f21])).
% 2.14/0.66  fof(f21,plain,(
% 2.14/0.66    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(flattening,[],[f20])).
% 2.14/0.66  fof(f20,plain,(
% 2.14/0.66    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.14/0.66    inference(ennf_transformation,[],[f10])).
% 2.14/0.66  fof(f10,axiom,(
% 2.14/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 2.14/0.66  fof(f85,plain,(
% 2.14/0.66    ( ! [X2] : (~r1_tarski(X2,k10_relat_1(sK0,sK2)) | r1_tarski(X2,sK1)) )),
% 2.14/0.66    inference(resolution,[],[f51,f34])).
% 2.14/0.66  fof(f34,plain,(
% 2.14/0.66    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.14/0.66    inference(cnf_transformation,[],[f29])).
% 2.14/0.66  fof(f51,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f26])).
% 2.14/0.66  fof(f26,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.14/0.66    inference(flattening,[],[f25])).
% 2.14/0.66  fof(f25,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.14/0.66    inference(ennf_transformation,[],[f3])).
% 2.14/0.66  fof(f3,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.14/0.66  fof(f74,plain,(
% 2.14/0.66    ~spl3_2 | ~spl3_1),
% 2.14/0.66    inference(avatar_split_clause,[],[f60,f66,f70])).
% 2.14/0.66  fof(f60,plain,(
% 2.14/0.66    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | ~r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2))),
% 2.14/0.66    inference(extensionality_resolution,[],[f48,f35])).
% 2.14/0.66  fof(f35,plain,(
% 2.14/0.66    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.14/0.66    inference(cnf_transformation,[],[f29])).
% 2.14/0.66  fof(f48,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f31])).
% 2.14/0.66  fof(f31,plain,(
% 2.14/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.66    inference(flattening,[],[f30])).
% 2.14/0.66  fof(f30,plain,(
% 2.14/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.66    inference(nnf_transformation,[],[f2])).
% 2.14/0.66  fof(f2,axiom,(
% 2.14/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.66  % SZS output end Proof for theBenchmark
% 2.14/0.66  % (4997)------------------------------
% 2.14/0.66  % (4997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (4997)Termination reason: Refutation
% 2.14/0.66  
% 2.14/0.66  % (4997)Memory used [KB]: 11129
% 2.14/0.66  % (4997)Time elapsed: 0.231 s
% 2.14/0.66  % (4997)------------------------------
% 2.14/0.66  % (4997)------------------------------
% 2.14/0.66  % (4990)Success in time 0.294 s
%------------------------------------------------------------------------------
