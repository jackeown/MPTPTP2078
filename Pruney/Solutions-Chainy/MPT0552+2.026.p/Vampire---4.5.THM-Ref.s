%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 236 expanded)
%              Number of leaves         :   20 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 ( 477 expanded)
%              Number of equality atoms :   19 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f54,f79,f90,f93,f136,f267,f292,f295,f304])).

fof(f304,plain,
    ( ~ spl3_10
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl3_10
    | spl3_12 ),
    inference(resolution,[],[f291,f266])).

fof(f266,plain,
    ( ! [X2,X1] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X1),X2),k7_relat_1(sK2,X2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl3_10
  <=> ! [X1,X2] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X1),X2),k7_relat_1(sK2,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f291,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl3_12
  <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f295,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f293,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f293,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(resolution,[],[f287,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f287,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl3_11
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f292,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f146,f76,f50,f289,f285])).

fof(f50,plain,
    ( spl3_2
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f76,plain,
    ( spl3_5
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f146,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_2
    | spl3_5 ),
    inference(forward_demodulation,[],[f143,f102])).

fof(f102,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(resolution,[],[f38,f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f143,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_2
    | spl3_5 ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0))
        | ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f51,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f32,f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))
        | ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f78,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f267,plain,
    ( ~ spl3_1
    | spl3_10 ),
    inference(avatar_split_clause,[],[f255,f265,f46])).

fof(f46,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f255,plain,(
    ! [X2,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(sK2,X1),X2),k7_relat_1(sK2,X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f183,f30])).

fof(f183,plain,(
    ! [X28,X27] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X27))
      | r1_tarski(k7_relat_1(k7_relat_1(sK2,X28),X27),k7_relat_1(sK2,X27)) ) ),
    inference(superposition,[],[f31,f154])).

fof(f154,plain,(
    ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2) ),
    inference(superposition,[],[f106,f102])).

fof(f106,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f102,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f136,plain,
    ( ~ spl3_6
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl3_6
    | spl3_7 ),
    inference(resolution,[],[f133,f84])).

fof(f84,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_6
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f133,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_7 ),
    inference(resolution,[],[f105,f31])).

fof(f105,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | spl3_7 ),
    inference(backward_demodulation,[],[f89,f102])).

fof(f89,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_7
  <=> r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f93,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f91,f23])).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(resolution,[],[f85,f30])).

fof(f85,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f90,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f81,f72,f50,f87,f83])).

fof(f72,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_2
    | spl3_4 ),
    inference(resolution,[],[f74,f55])).

fof(f74,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f62,f76,f72])).

fof(f62,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f24,f35,f35])).

fof(f24,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f48,f23])).

fof(f48,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f52,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f44,f50,f46])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k7_relat_1(sK2,X0),X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | ~ r1_tarski(k7_relat_1(sK2,X0),X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) ) ),
    inference(superposition,[],[f26,f40])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.41  % (31483)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.44  % (31483)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f305,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f52,f54,f79,f90,f93,f136,f267,f292,f295,f304])).
% 0.21/0.44  fof(f304,plain,(
% 0.21/0.44    ~spl3_10 | spl3_12),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.44  fof(f303,plain,(
% 0.21/0.44    $false | (~spl3_10 | spl3_12)),
% 0.21/0.44    inference(resolution,[],[f291,f266])).
% 0.21/0.44  fof(f266,plain,(
% 0.21/0.44    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X1),X2),k7_relat_1(sK2,X2))) ) | ~spl3_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f265])).
% 0.21/0.44  fof(f265,plain,(
% 0.21/0.44    spl3_10 <=> ! [X1,X2] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X1),X2),k7_relat_1(sK2,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f291,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) | spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f289])).
% 0.21/0.44  fof(f289,plain,(
% 0.21/0.44    spl3_12 <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f295,plain,(
% 0.21/0.44    spl3_11),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f294])).
% 0.21/0.44  fof(f294,plain,(
% 0.21/0.44    $false | spl3_11),
% 0.21/0.44    inference(resolution,[],[f293,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.44    inference(negated_conjecture,[],[f10])).
% 0.21/0.44  fof(f10,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.21/0.44  fof(f293,plain,(
% 0.21/0.44    ~v1_relat_1(sK2) | spl3_11),
% 0.21/0.44    inference(resolution,[],[f287,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.44  fof(f287,plain,(
% 0.21/0.44    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f285])).
% 0.21/0.44  fof(f285,plain,(
% 0.21/0.44    spl3_11 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f292,plain,(
% 0.21/0.44    ~spl3_11 | ~spl3_12 | ~spl3_2 | spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f146,f76,f50,f289,f285])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl3_2 <=> ! [X1,X0] : (~r1_tarski(k7_relat_1(sK2,X0),X1) | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    spl3_5 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl3_2 | spl3_5)),
% 0.21/0.44    inference(forward_demodulation,[],[f143,f102])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.44    inference(resolution,[],[f38,f23])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f33,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f29,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl3_2 | spl3_5)),
% 0.21/0.44    inference(resolution,[],[f78,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0)) | ~r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_2),
% 0.21/0.44    inference(superposition,[],[f51,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.21/0.44    inference(resolution,[],[f32,f23])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) | ~r1_tarski(k7_relat_1(sK2,X0),X1) | ~v1_relat_1(X1)) ) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f50])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f76])).
% 0.21/0.44  fof(f267,plain,(
% 0.21/0.44    ~spl3_1 | spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f255,f265,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f255,plain,(
% 0.21/0.44    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X1),X2),k7_relat_1(sK2,X2)) | ~v1_relat_1(sK2)) )),
% 0.21/0.44    inference(resolution,[],[f183,f30])).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    ( ! [X28,X27] : (~v1_relat_1(k7_relat_1(sK2,X27)) | r1_tarski(k7_relat_1(k7_relat_1(sK2,X28),X27),k7_relat_1(sK2,X27))) )),
% 0.21/0.44    inference(superposition,[],[f31,f154])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)) )),
% 0.21/0.44    inference(superposition,[],[f106,f102])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X1,X1,X0)))) )),
% 0.21/0.44    inference(superposition,[],[f102,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f27,f28,f28])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    ~spl3_6 | spl3_7),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    $false | (~spl3_6 | spl3_7)),
% 0.21/0.44    inference(resolution,[],[f133,f84])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f83])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl3_6 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_7),
% 0.21/0.44    inference(resolution,[],[f105,f31])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | spl3_7),
% 0.21/0.44    inference(backward_demodulation,[],[f89,f102])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK0)) | spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f87])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl3_7 <=> r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    $false | spl3_6),
% 0.21/0.44    inference(resolution,[],[f91,f23])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ~v1_relat_1(sK2) | spl3_6),
% 0.21/0.44    inference(resolution,[],[f85,f30])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f83])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    ~spl3_6 | ~spl3_7 | ~spl3_2 | spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f81,f72,f50,f87,f83])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl3_4 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | (~spl3_2 | spl3_4)),
% 0.21/0.44    inference(resolution,[],[f74,f55])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) | spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ~spl3_4 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f62,f76,f72])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 0.21/0.44    inference(resolution,[],[f39,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 0.21/0.44    inference(definition_unfolding,[],[f24,f35,f35])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    $false | spl3_1),
% 0.21/0.44    inference(resolution,[],[f48,f23])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f46])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ~spl3_1 | spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f44,f50,f46])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK2,X0),X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) | ~v1_relat_1(sK2)) )),
% 0.21/0.44    inference(resolution,[],[f42,f30])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK2,X0)) | ~r1_tarski(k7_relat_1(sK2,X0),X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))) )),
% 0.21/0.44    inference(superposition,[],[f26,f40])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31483)------------------------------
% 0.21/0.44  % (31483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31483)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31483)Memory used [KB]: 6268
% 0.21/0.44  % (31483)Time elapsed: 0.044 s
% 0.21/0.44  % (31483)------------------------------
% 0.21/0.44  % (31483)------------------------------
% 0.21/0.44  % (31477)Success in time 0.083 s
%------------------------------------------------------------------------------
