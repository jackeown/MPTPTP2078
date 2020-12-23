%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:04 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  129 (1435 expanded)
%              Number of leaves         :   19 ( 443 expanded)
%              Depth                    :   23
%              Number of atoms          :  285 (2481 expanded)
%              Number of equality atoms :  104 (1076 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f93,f204,f4623,f5194,f5195])).

fof(f5195,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f5135])).

fof(f5135,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f203,f5116])).

fof(f5116,plain,
    ( ! [X8,X7] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,X7)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f5115,f173])).

fof(f173,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f153,f125])).

fof(f125,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f58,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f153,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f5115,plain,
    ( ! [X8,X7] : k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X7),X8))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f5114,f585])).

fof(f585,plain,
    ( ! [X8,X9] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X8),X9)) = k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X8),X9))))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f577,f345])).

fof(f345,plain,
    ( ! [X2,X3] : k9_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3))
    | ~ spl3_1 ),
    inference(superposition,[],[f240,f181])).

fof(f181,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f240,plain,
    ( ! [X28,X29] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X28,X28,X29))) = k9_relat_1(k7_relat_1(sK2,X28),X29)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f232,f95])).

fof(f95,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f65,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f232,plain,
    ( ! [X28,X29] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X28,X28,X29))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X28),X29))
    | ~ spl3_1 ),
    inference(superposition,[],[f94,f205])).

fof(f205,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f94,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f38])).

fof(f577,plain,
    ( ! [X8,X9] : k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(sK2,X9)) = k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X8),X9))))
    | ~ spl3_1 ),
    inference(superposition,[],[f172,f223])).

fof(f223,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3))
    | ~ spl3_1 ),
    inference(superposition,[],[f205,f181])).

fof(f172,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f154,f126])).

fof(f126,plain,
    ( ! [X0,X1] : k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0)),X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f65,f49])).

fof(f154,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0)),X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f65,f50])).

fof(f5114,plain,
    ( ! [X8,X7] : k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))))) = k9_relat_1(k7_relat_1(sK2,X7),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X7),X8))))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f5054,f732])).

fof(f732,plain,
    ( ! [X0,X1] : k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))),X1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f721,f222])).

fof(f222,plain,
    ( ! [X1] : k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(sK2)) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f205,f137])).

fof(f137,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK2)))
    | ~ spl3_1 ),
    inference(superposition,[],[f125,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f34,f35,f35])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f721,plain,
    ( ! [X0,X1] : k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(sK2)),X1)
    | ~ spl3_1 ),
    inference(superposition,[],[f182,f125])).

fof(f182,plain,
    ( ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f65,f52])).

fof(f5054,plain,
    ( ! [X8,X7] : k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))))) = k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))),X8))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f919,f4579])).

fof(f4579,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f4558,f104])).

fof(f104,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f82,f94])).

fof(f82,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f65,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f4558,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0)))))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f65,f71,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f71,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f58,f63,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f919,plain,
    ( ! [X15,X16] : k9_relat_1(k7_relat_1(sK2,X16),X15) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X16))),X15)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f918,f221])).

fof(f221,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))
    | ~ spl3_1 ),
    inference(superposition,[],[f205,f125])).

fof(f918,plain,
    ( ! [X15,X16] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),X16),X15) = k9_relat_1(k7_relat_1(sK2,X16),X15)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f886,f915])).

fof(f915,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X1),X0) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))),X1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f881,f339])).

fof(f339,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X0),k1_relat_1(sK2))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f333,f240])).

fof(f333,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X0),k1_relat_1(sK2))
    | ~ spl3_1 ),
    inference(superposition,[],[f326,f219])).

fof(f219,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X1,X1,X0)))
    | ~ spl3_1 ),
    inference(superposition,[],[f205,f48])).

fof(f326,plain,
    ( ! [X33] : k9_relat_1(k7_relat_1(sK2,X33),k1_relat_1(sK2)) = k9_relat_1(sK2,X33)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f325,f173])).

fof(f325,plain,
    ( ! [X33] : k9_relat_1(k7_relat_1(sK2,X33),k1_relat_1(sK2)) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X33)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f322,f94])).

fof(f322,plain,
    ( ! [X33] : k9_relat_1(k7_relat_1(sK2,X33),k1_relat_1(sK2)) = k2_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X33))))
    | ~ spl3_1 ),
    inference(superposition,[],[f279,f221])).

fof(f279,plain,
    ( ! [X19,X18] : k9_relat_1(k7_relat_1(sK2,X18),X19) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X19),X18))
    | ~ spl3_1 ),
    inference(superposition,[],[f95,f248])).

fof(f248,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)
    | ~ spl3_1 ),
    inference(superposition,[],[f219,f205])).

fof(f881,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),k1_relat_1(sK2)) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))),X1)
    | ~ spl3_1 ),
    inference(superposition,[],[f804,f221])).

fof(f804,plain,
    ( ! [X88,X87,X89] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,X87),X88),X89) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X88),X89),X87)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f803,f205])).

fof(f803,plain,
    ( ! [X88,X87,X89] : k9_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X88,X88,X89))),X87) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X87),X88),X89)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f773,f96])).

fof(f96,plain,
    ( ! [X2,X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f67,f38])).

fof(f67,plain,
    ( ! [X0,X1] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f65,f37])).

fof(f773,plain,
    ( ! [X88,X87,X89] : k9_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X88,X88,X89))),X87) = k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X87),X88),X89))
    | ~ spl3_1 ),
    inference(superposition,[],[f279,f206])).

fof(f206,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k7_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f65,f53])).

fof(f886,plain,
    ( ! [X15,X16] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),X16),X15) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X15))),X16)
    | ~ spl3_1 ),
    inference(superposition,[],[f804,f222])).

fof(f203,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_4
  <=> k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f5194,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f5193])).

fof(f5193,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f5170])).

fof(f5170,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(superposition,[],[f203,f5116])).

fof(f4623,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f4599,f90,f61,f56,f4620])).

fof(f4620,plain,
    ( spl3_5
  <=> k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( spl3_3
  <=> k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f4599,plain,
    ( k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f4580,f125])).

fof(f4580,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f4557,f92])).

fof(f92,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f4557,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f58,f63,f51])).

fof(f204,plain,
    ( ~ spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f195,f56,f201])).

fof(f195,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f54,f181])).

fof(f54,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f47,f48])).

fof(f47,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) ),
    inference(definition_unfolding,[],[f32,f46,f46])).

fof(f32,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(f93,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f81,f56,f90])).

fof(f81,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f33])).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (16334)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (16343)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (16335)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (16342)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (16349)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (16338)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (16336)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (16348)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (16337)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (16346)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (16341)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (16350)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (16344)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (16333)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (16339)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (16347)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.24/0.51  % (16345)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.24/0.52  % (16351)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 3.31/0.80  % (16342)Refutation found. Thanks to Tanya!
% 3.31/0.80  % SZS status Theorem for theBenchmark
% 3.31/0.80  % SZS output start Proof for theBenchmark
% 3.31/0.80  fof(f5233,plain,(
% 3.31/0.80    $false),
% 3.31/0.80    inference(avatar_sat_refutation,[],[f59,f64,f93,f204,f4623,f5194,f5195])).
% 3.31/0.80  fof(f5195,plain,(
% 3.31/0.80    ~spl3_1 | ~spl3_2 | spl3_4),
% 3.31/0.80    inference(avatar_contradiction_clause,[],[f5135])).
% 3.31/0.80  fof(f5135,plain,(
% 3.31/0.80    $false | (~spl3_1 | ~spl3_2 | spl3_4)),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f203,f5116])).
% 3.31/0.80  fof(f5116,plain,(
% 3.31/0.80    ( ! [X8,X7] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,X7)))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(forward_demodulation,[],[f5115,f173])).
% 3.31/0.80  fof(f173,plain,(
% 3.31/0.80    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f153,f125])).
% 3.31/0.80  fof(f125,plain,(
% 3.31/0.80    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f49])).
% 3.31/0.80  fof(f49,plain,(
% 3.31/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 3.31/0.80    inference(definition_unfolding,[],[f39,f46])).
% 3.31/0.80  fof(f46,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.31/0.80    inference(definition_unfolding,[],[f36,f35])).
% 3.31/0.80  fof(f35,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f2])).
% 3.31/0.80  fof(f2,axiom,(
% 3.31/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.31/0.80  fof(f36,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f3])).
% 3.31/0.80  fof(f3,axiom,(
% 3.31/0.80    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.31/0.80  fof(f39,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f20])).
% 3.31/0.80  fof(f20,plain,(
% 3.31/0.80    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.31/0.80    inference(ennf_transformation,[],[f9])).
% 3.31/0.80  fof(f9,axiom,(
% 3.31/0.80    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 3.31/0.80  fof(f58,plain,(
% 3.31/0.80    v1_relat_1(sK2) | ~spl3_1),
% 3.31/0.80    inference(avatar_component_clause,[],[f56])).
% 3.31/0.80  fof(f56,plain,(
% 3.31/0.80    spl3_1 <=> v1_relat_1(sK2)),
% 3.31/0.80    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.31/0.80  fof(f153,plain,(
% 3.31/0.80    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f50])).
% 3.31/0.80  fof(f50,plain,(
% 3.31/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 3.31/0.80    inference(definition_unfolding,[],[f40,f46])).
% 3.31/0.80  fof(f40,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f21])).
% 3.31/0.80  fof(f21,plain,(
% 3.31/0.80    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/0.80    inference(ennf_transformation,[],[f6])).
% 3.31/0.80  fof(f6,axiom,(
% 3.31/0.80    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 3.31/0.80  fof(f5115,plain,(
% 3.31/0.80    ( ! [X8,X7] : (k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X7),X8))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(forward_demodulation,[],[f5114,f585])).
% 3.31/0.80  fof(f585,plain,(
% 3.31/0.80    ( ! [X8,X9] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X8),X9)) = k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X8),X9))))) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f577,f345])).
% 3.31/0.80  fof(f345,plain,(
% 3.31/0.80    ( ! [X2,X3] : (k9_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f240,f181])).
% 3.31/0.80  fof(f181,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f52])).
% 3.31/0.80  fof(f52,plain,(
% 3.31/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 3.31/0.80    inference(definition_unfolding,[],[f44,f46])).
% 3.31/0.80  fof(f44,plain,(
% 3.31/0.80    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f26])).
% 3.31/0.80  fof(f26,plain,(
% 3.31/0.80    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.31/0.80    inference(ennf_transformation,[],[f11])).
% 3.31/0.80  fof(f11,axiom,(
% 3.31/0.80    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 3.31/0.80  fof(f240,plain,(
% 3.31/0.80    ( ! [X28,X29] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X28,X28,X29))) = k9_relat_1(k7_relat_1(sK2,X28),X29)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f232,f95])).
% 3.31/0.80  fof(f95,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f38])).
% 3.31/0.80  fof(f38,plain,(
% 3.31/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 3.31/0.80    inference(cnf_transformation,[],[f19])).
% 3.31/0.80  fof(f19,plain,(
% 3.31/0.80    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.31/0.80    inference(ennf_transformation,[],[f8])).
% 3.31/0.80  fof(f8,axiom,(
% 3.31/0.80    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 3.31/0.80  fof(f65,plain,(
% 3.31/0.80    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f37])).
% 3.31/0.80  fof(f37,plain,(
% 3.31/0.80    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 3.31/0.80    inference(cnf_transformation,[],[f18])).
% 3.31/0.80  fof(f18,plain,(
% 3.31/0.80    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.31/0.80    inference(ennf_transformation,[],[f4])).
% 3.31/0.80  fof(f4,axiom,(
% 3.31/0.80    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.31/0.80  fof(f232,plain,(
% 3.31/0.80    ( ! [X28,X29] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X28,X28,X29))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X28),X29))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f94,f205])).
% 3.31/0.80  fof(f205,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f53])).
% 3.31/0.80  fof(f53,plain,(
% 3.31/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.31/0.80    inference(definition_unfolding,[],[f45,f46])).
% 3.31/0.80  fof(f45,plain,(
% 3.31/0.80    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f27])).
% 3.31/0.80  fof(f27,plain,(
% 3.31/0.80    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.31/0.80    inference(ennf_transformation,[],[f5])).
% 3.31/0.80  fof(f5,axiom,(
% 3.31/0.80    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 3.31/0.80  fof(f94,plain,(
% 3.31/0.80    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f38])).
% 3.31/0.80  fof(f577,plain,(
% 3.31/0.80    ( ! [X8,X9] : (k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(sK2,X9)) = k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X8),X9))))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f172,f223])).
% 3.31/0.80  fof(f223,plain,(
% 3.31/0.80    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f205,f181])).
% 3.31/0.80  fof(f172,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)))) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f154,f126])).
% 3.31/0.80  fof(f126,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0)),X1))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f49])).
% 3.31/0.80  fof(f154,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0)),X1)))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f50])).
% 3.31/0.80  fof(f5114,plain,(
% 3.31/0.80    ( ! [X8,X7] : (k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))))) = k9_relat_1(k7_relat_1(sK2,X7),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X7),X8))))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(forward_demodulation,[],[f5054,f732])).
% 3.31/0.80  fof(f732,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))),X1)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f721,f222])).
% 3.31/0.80  fof(f222,plain,(
% 3.31/0.80    ( ! [X1] : (k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(sK2)) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1)))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f205,f137])).
% 3.31/0.80  fof(f137,plain,(
% 3.31/0.80    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK2)))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f125,f48])).
% 3.31/0.80  fof(f48,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.31/0.80    inference(definition_unfolding,[],[f34,f35,f35])).
% 3.31/0.80  fof(f34,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f1])).
% 3.31/0.80  fof(f1,axiom,(
% 3.31/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.31/0.80  fof(f721,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(sK2)),X1)) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f182,f125])).
% 3.31/0.80  fof(f182,plain,(
% 3.31/0.80    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2)))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f52])).
% 3.31/0.80  fof(f5054,plain,(
% 3.31/0.80    ( ! [X8,X7] : (k1_setfam_1(k1_enumset1(X8,X8,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))))) = k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7))),X8))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(superposition,[],[f919,f4579])).
% 3.31/0.80  fof(f4579,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(forward_demodulation,[],[f4558,f104])).
% 3.31/0.80  fof(f104,plain,(
% 3.31/0.80    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)) ) | ~spl3_1),
% 3.31/0.80    inference(backward_demodulation,[],[f82,f94])).
% 3.31/0.80  fof(f82,plain,(
% 3.31/0.80    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f33])).
% 3.31/0.80  fof(f33,plain,(
% 3.31/0.80    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f17])).
% 3.31/0.80  fof(f17,plain,(
% 3.31/0.80    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.31/0.80    inference(ennf_transformation,[],[f7])).
% 3.31/0.80  fof(f7,axiom,(
% 3.31/0.80    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 3.31/0.80  fof(f4558,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0)))))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f71,f51])).
% 3.31/0.80  fof(f51,plain,(
% 3.31/0.80    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 3.31/0.80    inference(definition_unfolding,[],[f41,f46])).
% 3.31/0.80  fof(f41,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f23])).
% 3.31/0.80  fof(f23,plain,(
% 3.31/0.80    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.31/0.80    inference(flattening,[],[f22])).
% 3.31/0.80  fof(f22,plain,(
% 3.31/0.80    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.31/0.80    inference(ennf_transformation,[],[f12])).
% 3.31/0.80  fof(f12,axiom,(
% 3.31/0.80    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 3.31/0.80  fof(f71,plain,(
% 3.31/0.80    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f63,f43])).
% 3.31/0.80  fof(f43,plain,(
% 3.31/0.80    ( ! [X0,X1] : (~v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.31/0.80    inference(cnf_transformation,[],[f25])).
% 3.31/0.80  fof(f25,plain,(
% 3.31/0.80    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.31/0.80    inference(flattening,[],[f24])).
% 3.31/0.80  fof(f24,plain,(
% 3.31/0.80    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.31/0.80    inference(ennf_transformation,[],[f10])).
% 3.31/0.80  fof(f10,axiom,(
% 3.31/0.80    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 3.31/0.80  fof(f63,plain,(
% 3.31/0.80    v1_funct_1(sK2) | ~spl3_2),
% 3.31/0.80    inference(avatar_component_clause,[],[f61])).
% 3.31/0.80  fof(f61,plain,(
% 3.31/0.80    spl3_2 <=> v1_funct_1(sK2)),
% 3.31/0.80    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.31/0.80  fof(f919,plain,(
% 3.31/0.80    ( ! [X15,X16] : (k9_relat_1(k7_relat_1(sK2,X16),X15) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X16))),X15)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f918,f221])).
% 3.31/0.80  fof(f221,plain,(
% 3.31/0.80    ( ! [X0] : (k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f205,f125])).
% 3.31/0.80  fof(f918,plain,(
% 3.31/0.80    ( ! [X15,X16] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),X16),X15) = k9_relat_1(k7_relat_1(sK2,X16),X15)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f886,f915])).
% 3.31/0.80  fof(f915,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X1),X0) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))),X1)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f881,f339])).
% 3.31/0.80  fof(f339,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X0),k1_relat_1(sK2))) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f333,f240])).
% 3.31/0.80  fof(f333,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X0),k1_relat_1(sK2))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f326,f219])).
% 3.31/0.80  fof(f219,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X1,X1,X0)))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f205,f48])).
% 3.31/0.80  fof(f326,plain,(
% 3.31/0.80    ( ! [X33] : (k9_relat_1(k7_relat_1(sK2,X33),k1_relat_1(sK2)) = k9_relat_1(sK2,X33)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f325,f173])).
% 3.31/0.80  fof(f325,plain,(
% 3.31/0.80    ( ! [X33] : (k9_relat_1(k7_relat_1(sK2,X33),k1_relat_1(sK2)) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X33)))) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f322,f94])).
% 3.31/0.80  fof(f322,plain,(
% 3.31/0.80    ( ! [X33] : (k9_relat_1(k7_relat_1(sK2,X33),k1_relat_1(sK2)) = k2_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X33))))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f279,f221])).
% 3.31/0.80  fof(f279,plain,(
% 3.31/0.80    ( ! [X19,X18] : (k9_relat_1(k7_relat_1(sK2,X18),X19) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X19),X18))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f95,f248])).
% 3.31/0.80  fof(f248,plain,(
% 3.31/0.80    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f219,f205])).
% 3.31/0.80  fof(f881,plain,(
% 3.31/0.80    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),k1_relat_1(sK2)) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))),X1)) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f804,f221])).
% 3.31/0.80  fof(f804,plain,(
% 3.31/0.80    ( ! [X88,X87,X89] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,X87),X88),X89) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X88),X89),X87)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f803,f205])).
% 3.31/0.80  fof(f803,plain,(
% 3.31/0.80    ( ! [X88,X87,X89] : (k9_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X88,X88,X89))),X87) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X87),X88),X89)) ) | ~spl3_1),
% 3.31/0.80    inference(forward_demodulation,[],[f773,f96])).
% 3.31/0.80  fof(f96,plain,(
% 3.31/0.80    ( ! [X2,X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2)) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f67,f38])).
% 3.31/0.80  fof(f67,plain,(
% 3.31/0.80    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f37])).
% 3.31/0.80  fof(f773,plain,(
% 3.31/0.80    ( ! [X88,X87,X89] : (k9_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X88,X88,X89))),X87) = k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X87),X88),X89))) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f279,f206])).
% 3.31/0.80  fof(f206,plain,(
% 3.31/0.80    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k7_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(X1,X1,X2)))) ) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f65,f53])).
% 3.31/0.80  fof(f886,plain,(
% 3.31/0.80    ( ! [X15,X16] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),X16),X15) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X15))),X16)) ) | ~spl3_1),
% 3.31/0.80    inference(superposition,[],[f804,f222])).
% 3.31/0.80  fof(f203,plain,(
% 3.31/0.80    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) | spl3_4),
% 3.31/0.80    inference(avatar_component_clause,[],[f201])).
% 3.31/0.80  fof(f201,plain,(
% 3.31/0.80    spl3_4 <=> k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 3.31/0.80    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.31/0.80  fof(f5194,plain,(
% 3.31/0.80    ~spl3_1 | ~spl3_2 | spl3_4),
% 3.31/0.80    inference(avatar_contradiction_clause,[],[f5193])).
% 3.31/0.80  fof(f5193,plain,(
% 3.31/0.80    $false | (~spl3_1 | ~spl3_2 | spl3_4)),
% 3.31/0.80    inference(trivial_inequality_removal,[],[f5170])).
% 3.31/0.80  fof(f5170,plain,(
% 3.31/0.80    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) | (~spl3_1 | ~spl3_2 | spl3_4)),
% 3.31/0.80    inference(superposition,[],[f203,f5116])).
% 3.31/0.80  fof(f4623,plain,(
% 3.31/0.80    spl3_5 | ~spl3_1 | ~spl3_2 | ~spl3_3),
% 3.31/0.80    inference(avatar_split_clause,[],[f4599,f90,f61,f56,f4620])).
% 3.31/0.80  fof(f4620,plain,(
% 3.31/0.80    spl3_5 <=> k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK2)))),
% 3.31/0.80    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.31/0.80  fof(f90,plain,(
% 3.31/0.80    spl3_3 <=> k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)),
% 3.31/0.80    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.31/0.80  fof(f4599,plain,(
% 3.31/0.80    k1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK2))) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 3.31/0.80    inference(superposition,[],[f4580,f125])).
% 3.31/0.80  fof(f4580,plain,(
% 3.31/0.80    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 3.31/0.80    inference(forward_demodulation,[],[f4557,f92])).
% 3.31/0.80  fof(f92,plain,(
% 3.31/0.80    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) | ~spl3_3),
% 3.31/0.80    inference(avatar_component_clause,[],[f90])).
% 3.31/0.80  fof(f4557,plain,(
% 3.31/0.80    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2))))) ) | (~spl3_1 | ~spl3_2)),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f63,f51])).
% 3.31/0.80  fof(f204,plain,(
% 3.31/0.80    ~spl3_4 | ~spl3_1),
% 3.31/0.80    inference(avatar_split_clause,[],[f195,f56,f201])).
% 3.31/0.80  fof(f195,plain,(
% 3.31/0.80    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) | ~spl3_1),
% 3.31/0.80    inference(backward_demodulation,[],[f54,f181])).
% 3.31/0.80  fof(f54,plain,(
% 3.31/0.80    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),
% 3.31/0.80    inference(backward_demodulation,[],[f47,f48])).
% 3.31/0.80  fof(f47,plain,(
% 3.31/0.80    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),
% 3.31/0.80    inference(definition_unfolding,[],[f32,f46,f46])).
% 3.31/0.80  fof(f32,plain,(
% 3.31/0.80    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 3.31/0.80    inference(cnf_transformation,[],[f29])).
% 3.31/0.80  fof(f29,plain,(
% 3.31/0.80    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.31/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).
% 3.31/0.80  fof(f28,plain,(
% 3.31/0.80    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.31/0.80    introduced(choice_axiom,[])).
% 3.31/0.80  fof(f16,plain,(
% 3.31/0.80    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.31/0.80    inference(flattening,[],[f15])).
% 3.31/0.80  fof(f15,plain,(
% 3.31/0.80    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.31/0.80    inference(ennf_transformation,[],[f14])).
% 3.31/0.80  fof(f14,negated_conjecture,(
% 3.31/0.80    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 3.31/0.80    inference(negated_conjecture,[],[f13])).
% 3.31/0.80  fof(f13,conjecture,(
% 3.31/0.80    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 3.31/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).
% 3.31/0.80  fof(f93,plain,(
% 3.31/0.80    spl3_3 | ~spl3_1),
% 3.31/0.80    inference(avatar_split_clause,[],[f81,f56,f90])).
% 3.31/0.80  fof(f81,plain,(
% 3.31/0.80    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) | ~spl3_1),
% 3.31/0.80    inference(unit_resulting_resolution,[],[f58,f33])).
% 3.31/0.80  fof(f64,plain,(
% 3.31/0.80    spl3_2),
% 3.31/0.80    inference(avatar_split_clause,[],[f31,f61])).
% 3.31/0.80  fof(f31,plain,(
% 3.31/0.80    v1_funct_1(sK2)),
% 3.31/0.80    inference(cnf_transformation,[],[f29])).
% 3.31/0.80  fof(f59,plain,(
% 3.31/0.80    spl3_1),
% 3.31/0.80    inference(avatar_split_clause,[],[f30,f56])).
% 3.31/0.80  fof(f30,plain,(
% 3.31/0.80    v1_relat_1(sK2)),
% 3.31/0.80    inference(cnf_transformation,[],[f29])).
% 3.31/0.80  % SZS output end Proof for theBenchmark
% 3.31/0.80  % (16342)------------------------------
% 3.31/0.80  % (16342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.80  % (16342)Termination reason: Refutation
% 3.31/0.80  
% 3.31/0.80  % (16342)Memory used [KB]: 11513
% 3.31/0.80  % (16342)Time elapsed: 0.376 s
% 3.31/0.80  % (16342)------------------------------
% 3.31/0.80  % (16342)------------------------------
% 3.31/0.80  % (16332)Success in time 0.448 s
%------------------------------------------------------------------------------
