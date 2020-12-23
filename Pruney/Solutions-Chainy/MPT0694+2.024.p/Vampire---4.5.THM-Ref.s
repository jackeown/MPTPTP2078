%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 223 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  156 ( 352 expanded)
%              Number of equality atoms :   22 ( 137 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f82,f88,f105,f287])).

fof(f287,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f282,f62])).

fof(f62,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f53,f58,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f58,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f282,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | ~ spl3_1
    | spl3_5 ),
    inference(superposition,[],[f106,f127])).

fof(f127,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,X0) = k2_xboole_0(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))),k9_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f53,f70,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(resolution,[],[f37,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f70,plain,(
    ! [X4,X3] : r1_tarski(k1_setfam_1(k4_enumset1(X4,X4,X4,X4,X4,X3)),X3) ),
    inference(superposition,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f31,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f106,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X0),sK1)
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f104,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f104,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_5
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f105,plain,
    ( ~ spl3_5
    | ~ spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f91,f85,f51,f102])).

fof(f85,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f91,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f90,f64])).

fof(f64,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k9_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f53,f47,f37])).

fof(f90,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_4 ),
    inference(resolution,[],[f87,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f87,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f88,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f83,f79,f85])).

fof(f79,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0))))
    | spl3_3 ),
    inference(forward_demodulation,[],[f81,f48])).

fof(f81,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f46,f79])).

fof(f46,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f29,f45,f45])).

fof(f29,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (8639)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (8631)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (8639)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f288,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f54,f59,f82,f88,f105,f287])).
% 0.21/0.44  fof(f287,plain,(
% 0.21/0.44    ~spl3_1 | ~spl3_2 | spl3_5),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f286])).
% 0.21/0.44  fof(f286,plain,(
% 0.21/0.44    $false | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f282,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f53,f58,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    v1_funct_1(sK2) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl3_2 <=> v1_funct_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f282,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) | (~spl3_1 | spl3_5)),
% 0.21/0.45    inference(superposition,[],[f106,f127])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k9_relat_1(sK2,X0) = k2_xboole_0(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))),k9_relat_1(sK2,X0))) ) | ~spl3_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f53,f70,f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.45    inference(resolution,[],[f37,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X4,X3] : (r1_tarski(k1_setfam_1(k4_enumset1(X4,X4,X4,X4,X4,X3)),X3)) )),
% 0.21/0.45    inference(superposition,[],[f47,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f31,f45,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f33,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f36,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f40,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f30,f45])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(k2_xboole_0(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X0),sK1)) ) | spl3_5),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f104,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl3_5 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    ~spl3_5 | ~spl3_1 | spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f91,f85,f51,f102])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl3_4 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) | (~spl3_1 | spl3_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f90,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k9_relat_1(sK2,X0))) ) | ~spl3_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f53,f47,f37])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_4),
% 0.21/0.45    inference(resolution,[],[f87,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f39,f45])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) | spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f85])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ~spl3_4 | spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f83,f79,f85])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl3_3 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) | spl3_3),
% 0.21/0.45    inference(forward_demodulation,[],[f81,f48])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f46,f79])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 0.21/0.45    inference(definition_unfolding,[],[f29,f45,f45])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f13])).
% 0.21/0.45  fof(f13,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f56])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    v1_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (8639)------------------------------
% 0.21/0.45  % (8639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (8639)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (8639)Memory used [KB]: 11001
% 0.21/0.45  % (8639)Time elapsed: 0.026 s
% 0.21/0.45  % (8639)------------------------------
% 0.21/0.45  % (8639)------------------------------
% 0.21/0.45  % (8623)Success in time 0.089 s
%------------------------------------------------------------------------------
