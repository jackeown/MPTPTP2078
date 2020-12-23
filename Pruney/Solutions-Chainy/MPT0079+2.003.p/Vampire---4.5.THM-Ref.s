%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:51 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 524 expanded)
%              Number of leaves         :   21 ( 158 expanded)
%              Depth                    :   18
%              Number of atoms          :  264 (1181 expanded)
%              Number of equality atoms :   84 ( 565 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1912,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f208,f241,f528,f570,f664,f665,f1127,f1517,f1906])).

fof(f1906,plain,
    ( ~ spl4_16
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(avatar_contradiction_clause,[],[f1905])).

fof(f1905,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f1904,f469])).

fof(f469,plain,(
    ! [X0] : r1_tarski(sK1,k2_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f346,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f346,plain,(
    r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f28,f224])).

fof(f224,plain,(
    sK1 = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f213,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f213,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f39,f91])).

fof(f91,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f25,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1904,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl4_16
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f1898,f1025])).

fof(f1025,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1017,f26])).

fof(f26,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f1017,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_16 ),
    inference(superposition,[],[f545,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f545,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f376,f205])).

fof(f205,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_16
  <=> sK2 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f376,plain,(
    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f130,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f130,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f59,f34])).

fof(f59,plain,(
    r1_tarski(k4_xboole_0(sK2,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f44,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f1898,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl4_16
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(superposition,[],[f1759,f1552])).

fof(f1552,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl4_32
    | ~ spl4_47 ),
    inference(backward_demodulation,[],[f460,f1125])).

fof(f1125,plain,
    ( sK0 = sK3
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1123,plain,
    ( spl4_47
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f460,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl4_32
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1759,plain,
    ( ! [X1] :
        ( r1_tarski(k4_xboole_0(X1,sK0),sK2)
        | ~ r1_tarski(X1,k2_xboole_0(sK0,sK1)) )
    | ~ spl4_16
    | ~ spl4_30
    | ~ spl4_47 ),
    inference(backward_demodulation,[],[f1646,f1754])).

fof(f1754,plain,
    ( sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl4_30
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f1750,f438])).

fof(f438,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl4_30
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1750,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl4_47 ),
    inference(superposition,[],[f32,f1730])).

fof(f1730,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)
    | ~ spl4_47 ),
    inference(superposition,[],[f1518,f30])).

fof(f1518,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)
    | ~ spl4_47 ),
    inference(backward_demodulation,[],[f23,f1125])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1646,plain,
    ( ! [X1] :
        ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
        | ~ r1_tarski(X1,k2_xboole_0(sK0,sK1)) )
    | ~ spl4_16
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f1645,f1633])).

fof(f1633,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))
    | ~ spl4_16
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f1526,f205])).

fof(f1526,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))
    | ~ spl4_47 ),
    inference(backward_demodulation,[],[f114,f1125])).

fof(f114,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f38,f45])).

fof(f45,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f32,f23])).

fof(f1645,plain,
    ( ! [X1] :
        ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),sK2)
        | ~ r1_tarski(X1,k2_xboole_0(sK0,sK1)) )
    | ~ spl4_16
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f1543,f205])).

fof(f1543,plain,
    ( ! [X1] :
        ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),k4_xboole_0(sK2,sK0))
        | ~ r1_tarski(X1,k2_xboole_0(sK0,sK1)) )
    | ~ spl4_47 ),
    inference(backward_demodulation,[],[f279,f1125])).

fof(f279,plain,(
    ! [X1] :
      ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)))),k4_xboole_0(sK2,sK3))
      | ~ r1_tarski(X1,k2_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f37,f125])).

fof(f125,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK2,sK3)) ),
    inference(backward_demodulation,[],[f113,f114])).

fof(f113,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f39,f45])).

fof(f1517,plain,
    ( ~ spl4_20
    | spl4_46 ),
    inference(avatar_contradiction_clause,[],[f1516])).

fof(f1516,plain,
    ( $false
    | ~ spl4_20
    | spl4_46 ),
    inference(subsumption_resolution,[],[f1515,f300])).

fof(f300,plain,(
    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f149,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,k2_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f36,f23])).

fof(f149,plain,(
    r1_tarski(sK3,sK3) ),
    inference(superposition,[],[f28,f109])).

fof(f109,plain,(
    sK3 = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f98,f27])).

fof(f98,plain,(
    sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f39,f42])).

fof(f1515,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_20
    | spl4_46 ),
    inference(forward_demodulation,[],[f1513,f30])).

fof(f1513,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK1,sK0))
    | ~ spl4_20
    | spl4_46 ),
    inference(unit_resulting_resolution,[],[f1121,f622])).

fof(f622,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k2_xboole_0(sK1,X0))
        | r1_tarski(sK3,X0) )
    | ~ spl4_20 ),
    inference(superposition,[],[f37,f238])).

fof(f238,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl4_20
  <=> sK3 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1121,plain,
    ( ~ r1_tarski(sK3,sK0)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f1119,plain,
    ( spl4_46
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f1127,plain,
    ( ~ spl4_46
    | spl4_47
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f1115,f436,f1123,f1119])).

fof(f1115,plain,
    ( sK0 = sK3
    | ~ r1_tarski(sK3,sK0)
    | ~ spl4_30 ),
    inference(superposition,[],[f34,f696])).

fof(f696,plain,
    ( sK3 = k2_xboole_0(sK3,sK0)
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f398,f438])).

fof(f398,plain,(
    sK3 = k2_xboole_0(sK3,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f164,f30])).

fof(f164,plain,(
    sK3 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f126,f34])).

fof(f126,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f28,f48])).

fof(f48,plain,(
    ! [X1] :
      ( r1_tarski(k4_xboole_0(X1,sK2),sK3)
      | ~ r1_tarski(X1,k2_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f37,f23])).

fof(f665,plain,
    ( spl4_32
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f652,f203,f458])).

fof(f652,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_16 ),
    inference(superposition,[],[f210,f603])).

fof(f603,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f568,f34])).

fof(f568,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f532,f28])).

fof(f532,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k2_xboole_0(sK2,X0))
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f77,f205])).

fof(f77,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ r1_tarski(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) ) ),
    inference(superposition,[],[f37,f41])).

fof(f41,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f40])).

fof(f24,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f210,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f39,f91])).

fof(f664,plain,
    ( spl4_30
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f651,f203,f436])).

fof(f651,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_16 ),
    inference(superposition,[],[f177,f603])).

fof(f177,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f39,f72])).

fof(f72,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f41,f38])).

fof(f570,plain,
    ( ~ spl4_16
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl4_16
    | spl4_19 ),
    inference(subsumption_resolution,[],[f539,f28])).

fof(f539,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,k4_xboole_0(sK3,sK1)))
    | ~ spl4_16
    | spl4_19 ),
    inference(backward_demodulation,[],[f361,f205])).

fof(f361,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK3,sK1)))
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f234,f77])).

fof(f234,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK3,sK1))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl4_19
  <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f528,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f520,f199])).

fof(f199,plain,
    ( spl4_15
  <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f520,plain,(
    r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f193,f209])).

fof(f209,plain,(
    ! [X1] :
      ( r1_tarski(X1,k4_xboole_0(sK2,sK0))
      | ~ r1_tarski(X1,sK2) ) ),
    inference(forward_demodulation,[],[f197,f27])).

fof(f197,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | r1_tarski(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(sK2,sK0)) ) ),
    inference(superposition,[],[f37,f74])).

fof(f74,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f39,f41])).

fof(f193,plain,(
    r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f28,f74])).

fof(f241,plain,
    ( ~ spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f228,f236,f232])).

fof(f228,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f34,f93])).

fof(f93,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f39,f42])).

fof(f208,plain,
    ( ~ spl4_15
    | spl4_16 ),
    inference(avatar_split_clause,[],[f195,f203,f199])).

fof(f195,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f34,f74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (24554)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (24567)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (24566)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (24543)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (24545)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (24542)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (24548)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (24559)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (24569)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (24558)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (24563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (24546)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (24541)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (24570)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (24555)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (24561)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (24544)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (24547)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (24558)Refutation not found, incomplete strategy% (24558)------------------------------
% 0.21/0.52  % (24558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24562)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (24557)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (24558)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24558)Memory used [KB]: 10618
% 0.21/0.52  % (24558)Time elapsed: 0.113 s
% 0.21/0.52  % (24558)------------------------------
% 0.21/0.52  % (24558)------------------------------
% 0.21/0.52  % (24549)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (24550)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (24552)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (24553)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (24552)Refutation not found, incomplete strategy% (24552)------------------------------
% 0.21/0.53  % (24552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24552)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24552)Memory used [KB]: 10618
% 0.21/0.53  % (24552)Time elapsed: 0.136 s
% 0.21/0.53  % (24552)------------------------------
% 0.21/0.53  % (24552)------------------------------
% 0.21/0.53  % (24568)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (24551)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (24564)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (24565)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (24556)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (24556)Refutation not found, incomplete strategy% (24556)------------------------------
% 0.21/0.54  % (24556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24556)Memory used [KB]: 6140
% 0.21/0.54  % (24556)Time elapsed: 0.003 s
% 0.21/0.54  % (24556)------------------------------
% 0.21/0.54  % (24556)------------------------------
% 0.21/0.54  % (24560)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (24551)Refutation not found, incomplete strategy% (24551)------------------------------
% 0.21/0.54  % (24551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24551)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24551)Memory used [KB]: 10618
% 0.21/0.54  % (24551)Time elapsed: 0.153 s
% 0.21/0.54  % (24551)------------------------------
% 0.21/0.54  % (24551)------------------------------
% 1.68/0.60  % (24567)Refutation found. Thanks to Tanya!
% 1.68/0.60  % SZS status Theorem for theBenchmark
% 1.68/0.60  % SZS output start Proof for theBenchmark
% 1.68/0.60  fof(f1912,plain,(
% 1.68/0.60    $false),
% 1.68/0.60    inference(avatar_sat_refutation,[],[f208,f241,f528,f570,f664,f665,f1127,f1517,f1906])).
% 1.68/0.60  fof(f1906,plain,(
% 1.68/0.60    ~spl4_16 | ~spl4_30 | ~spl4_32 | ~spl4_47),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f1905])).
% 1.68/0.60  fof(f1905,plain,(
% 1.68/0.60    $false | (~spl4_16 | ~spl4_30 | ~spl4_32 | ~spl4_47)),
% 1.68/0.60    inference(subsumption_resolution,[],[f1904,f469])).
% 1.68/0.60  fof(f469,plain,(
% 1.68/0.60    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(X0,sK1))) )),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f346,f36])).
% 1.68/0.60  fof(f36,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f19])).
% 1.68/0.60  fof(f19,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.68/0.60    inference(ennf_transformation,[],[f4])).
% 1.68/0.60  fof(f4,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.68/0.60  fof(f346,plain,(
% 1.68/0.60    r1_tarski(sK1,sK1)),
% 1.68/0.60    inference(superposition,[],[f28,f224])).
% 1.68/0.60  fof(f224,plain,(
% 1.68/0.60    sK1 = k2_xboole_0(sK1,k1_xboole_0)),
% 1.68/0.60    inference(forward_demodulation,[],[f213,f27])).
% 1.68/0.60  fof(f27,plain,(
% 1.68/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.60    inference(cnf_transformation,[],[f6])).
% 1.68/0.60  fof(f6,axiom,(
% 1.68/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.68/0.60  fof(f213,plain,(
% 1.68/0.60    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)),
% 1.68/0.60    inference(superposition,[],[f39,f91])).
% 1.68/0.60  fof(f91,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.68/0.60    inference(superposition,[],[f42,f38])).
% 1.68/0.60  fof(f38,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.68/0.60    inference(definition_unfolding,[],[f29,f31,f31])).
% 1.68/0.60  fof(f31,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f9])).
% 1.68/0.60  fof(f9,axiom,(
% 1.68/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.68/0.60  fof(f29,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f2])).
% 1.68/0.60  fof(f2,axiom,(
% 1.68/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.68/0.60  fof(f42,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f25,f40])).
% 1.68/0.60  fof(f40,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f35,f31])).
% 1.68/0.60  fof(f35,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f18])).
% 1.68/0.60  fof(f18,plain,(
% 1.68/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.68/0.60    inference(ennf_transformation,[],[f14])).
% 1.68/0.60  fof(f14,plain,(
% 1.68/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.68/0.60    inference(unused_predicate_definition_removal,[],[f3])).
% 1.68/0.60  fof(f3,axiom,(
% 1.68/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.68/0.60  fof(f25,plain,(
% 1.68/0.60    r1_xboole_0(sK3,sK1)),
% 1.68/0.60    inference(cnf_transformation,[],[f22])).
% 1.68/0.60  fof(f22,plain,(
% 1.68/0.60    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f21])).
% 1.68/0.60  fof(f21,plain,(
% 1.68/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f16,plain,(
% 1.68/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.68/0.60    inference(flattening,[],[f15])).
% 1.68/0.60  fof(f15,plain,(
% 1.68/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.68/0.60    inference(ennf_transformation,[],[f13])).
% 1.68/0.60  fof(f13,negated_conjecture,(
% 1.68/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.68/0.60    inference(negated_conjecture,[],[f12])).
% 1.68/0.60  fof(f12,conjecture,(
% 1.68/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.68/0.60  fof(f39,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.68/0.60    inference(definition_unfolding,[],[f33,f31])).
% 1.68/0.60  fof(f33,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.68/0.60    inference(cnf_transformation,[],[f10])).
% 1.68/0.60  fof(f10,axiom,(
% 1.68/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.68/0.60  fof(f28,plain,(
% 1.68/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f11])).
% 1.68/0.60  fof(f11,axiom,(
% 1.68/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.68/0.60  fof(f1904,plain,(
% 1.68/0.60    ~r1_tarski(sK1,k2_xboole_0(sK0,sK1)) | (~spl4_16 | ~spl4_30 | ~spl4_32 | ~spl4_47)),
% 1.68/0.60    inference(subsumption_resolution,[],[f1898,f1025])).
% 1.68/0.60  fof(f1025,plain,(
% 1.68/0.60    ~r1_tarski(sK1,sK2) | ~spl4_16),
% 1.68/0.60    inference(subsumption_resolution,[],[f1017,f26])).
% 1.68/0.60  fof(f26,plain,(
% 1.68/0.60    sK1 != sK2),
% 1.68/0.60    inference(cnf_transformation,[],[f22])).
% 1.68/0.60  fof(f1017,plain,(
% 1.68/0.60    sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl4_16),
% 1.68/0.60    inference(superposition,[],[f545,f34])).
% 1.68/0.60  fof(f34,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f17])).
% 1.68/0.60  fof(f17,plain,(
% 1.68/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.68/0.60    inference(ennf_transformation,[],[f5])).
% 1.68/0.60  fof(f5,axiom,(
% 1.68/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.68/0.60  fof(f545,plain,(
% 1.68/0.60    sK1 = k2_xboole_0(sK1,sK2) | ~spl4_16),
% 1.68/0.60    inference(backward_demodulation,[],[f376,f205])).
% 1.68/0.60  fof(f205,plain,(
% 1.68/0.60    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_16),
% 1.68/0.60    inference(avatar_component_clause,[],[f203])).
% 1.68/0.60  fof(f203,plain,(
% 1.68/0.60    spl4_16 <=> sK2 = k4_xboole_0(sK2,sK0)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.68/0.60  fof(f376,plain,(
% 1.68/0.60    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),
% 1.68/0.60    inference(superposition,[],[f130,f30])).
% 1.68/0.60  fof(f30,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f1])).
% 1.68/0.60  fof(f1,axiom,(
% 1.68/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.68/0.60  fof(f130,plain,(
% 1.68/0.60    sK1 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK1)),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f59,f34])).
% 1.68/0.60  fof(f59,plain,(
% 1.68/0.60    r1_tarski(k4_xboole_0(sK2,sK0),sK1)),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f44,f37])).
% 1.68/0.60  fof(f37,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f20])).
% 1.68/0.60  fof(f20,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.68/0.60    inference(ennf_transformation,[],[f8])).
% 1.68/0.60  fof(f8,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.68/0.60  fof(f44,plain,(
% 1.68/0.60    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.68/0.60    inference(superposition,[],[f28,f23])).
% 1.68/0.60  fof(f23,plain,(
% 1.68/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.68/0.60    inference(cnf_transformation,[],[f22])).
% 1.68/0.60  fof(f1898,plain,(
% 1.68/0.60    r1_tarski(sK1,sK2) | ~r1_tarski(sK1,k2_xboole_0(sK0,sK1)) | (~spl4_16 | ~spl4_30 | ~spl4_32 | ~spl4_47)),
% 1.68/0.60    inference(superposition,[],[f1759,f1552])).
% 1.68/0.60  fof(f1552,plain,(
% 1.68/0.60    sK1 = k4_xboole_0(sK1,sK0) | (~spl4_32 | ~spl4_47)),
% 1.68/0.60    inference(backward_demodulation,[],[f460,f1125])).
% 1.68/0.60  fof(f1125,plain,(
% 1.68/0.60    sK0 = sK3 | ~spl4_47),
% 1.68/0.60    inference(avatar_component_clause,[],[f1123])).
% 1.68/0.60  fof(f1123,plain,(
% 1.68/0.60    spl4_47 <=> sK0 = sK3),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.68/0.60  fof(f460,plain,(
% 1.68/0.60    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_32),
% 1.68/0.60    inference(avatar_component_clause,[],[f458])).
% 1.68/0.60  fof(f458,plain,(
% 1.68/0.60    spl4_32 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.68/0.60  fof(f1759,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,sK0),sK2) | ~r1_tarski(X1,k2_xboole_0(sK0,sK1))) ) | (~spl4_16 | ~spl4_30 | ~spl4_47)),
% 1.68/0.60    inference(backward_demodulation,[],[f1646,f1754])).
% 1.68/0.60  fof(f1754,plain,(
% 1.68/0.60    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) | (~spl4_30 | ~spl4_47)),
% 1.68/0.60    inference(forward_demodulation,[],[f1750,f438])).
% 1.68/0.60  fof(f438,plain,(
% 1.68/0.60    sK0 = k4_xboole_0(sK0,sK2) | ~spl4_30),
% 1.68/0.60    inference(avatar_component_clause,[],[f436])).
% 1.68/0.60  fof(f436,plain,(
% 1.68/0.60    spl4_30 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.68/0.60  fof(f1750,plain,(
% 1.68/0.60    k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) | ~spl4_47),
% 1.68/0.60    inference(superposition,[],[f32,f1730])).
% 1.68/0.60  fof(f1730,plain,(
% 1.68/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) | ~spl4_47),
% 1.68/0.60    inference(superposition,[],[f1518,f30])).
% 1.68/0.60  fof(f1518,plain,(
% 1.68/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) | ~spl4_47),
% 1.68/0.60    inference(backward_demodulation,[],[f23,f1125])).
% 1.68/0.60  fof(f32,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f7])).
% 1.68/0.60  fof(f7,axiom,(
% 1.68/0.60    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.68/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.68/0.60  fof(f1646,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) | ~r1_tarski(X1,k2_xboole_0(sK0,sK1))) ) | (~spl4_16 | ~spl4_47)),
% 1.68/0.60    inference(forward_demodulation,[],[f1645,f1633])).
% 1.68/0.60  fof(f1633,plain,(
% 1.68/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) | (~spl4_16 | ~spl4_47)),
% 1.68/0.60    inference(forward_demodulation,[],[f1526,f205])).
% 1.68/0.60  fof(f1526,plain,(
% 1.68/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) | ~spl4_47),
% 1.68/0.60    inference(backward_demodulation,[],[f114,f1125])).
% 1.68/0.60  fof(f114,plain,(
% 1.68/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)))),
% 1.68/0.60    inference(superposition,[],[f38,f45])).
% 1.68/0.60  fof(f45,plain,(
% 1.68/0.60    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.68/0.60    inference(superposition,[],[f32,f23])).
% 1.68/0.60  fof(f1645,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),sK2) | ~r1_tarski(X1,k2_xboole_0(sK0,sK1))) ) | (~spl4_16 | ~spl4_47)),
% 1.68/0.60    inference(forward_demodulation,[],[f1543,f205])).
% 1.68/0.60  fof(f1543,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),k4_xboole_0(sK2,sK0)) | ~r1_tarski(X1,k2_xboole_0(sK0,sK1))) ) | ~spl4_47),
% 1.68/0.60    inference(backward_demodulation,[],[f279,f1125])).
% 1.68/0.60  fof(f279,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)))),k4_xboole_0(sK2,sK3)) | ~r1_tarski(X1,k2_xboole_0(sK0,sK1))) )),
% 1.68/0.60    inference(superposition,[],[f37,f125])).
% 1.68/0.60  fof(f125,plain,(
% 1.68/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK2,sK3))),
% 1.68/0.60    inference(backward_demodulation,[],[f113,f114])).
% 1.68/0.60  fof(f113,plain,(
% 1.68/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3))),
% 1.68/0.60    inference(superposition,[],[f39,f45])).
% 1.68/0.60  fof(f1517,plain,(
% 1.68/0.60    ~spl4_20 | spl4_46),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f1516])).
% 1.68/0.60  fof(f1516,plain,(
% 1.68/0.60    $false | (~spl4_20 | spl4_46)),
% 1.68/0.60    inference(subsumption_resolution,[],[f1515,f300])).
% 1.68/0.60  fof(f300,plain,(
% 1.68/0.60    r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f149,f47])).
% 1.68/0.60  fof(f47,plain,(
% 1.68/0.60    ( ! [X0] : (~r1_tarski(X0,sK3) | r1_tarski(X0,k2_xboole_0(sK0,sK1))) )),
% 1.68/0.60    inference(superposition,[],[f36,f23])).
% 1.68/0.60  fof(f149,plain,(
% 1.68/0.60    r1_tarski(sK3,sK3)),
% 1.68/0.60    inference(superposition,[],[f28,f109])).
% 1.68/0.60  fof(f109,plain,(
% 1.68/0.60    sK3 = k2_xboole_0(sK3,k1_xboole_0)),
% 1.68/0.60    inference(forward_demodulation,[],[f98,f27])).
% 1.68/0.60  fof(f98,plain,(
% 1.68/0.60    sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0)),
% 1.68/0.60    inference(superposition,[],[f39,f42])).
% 1.68/0.60  fof(f1515,plain,(
% 1.68/0.60    ~r1_tarski(sK3,k2_xboole_0(sK0,sK1)) | (~spl4_20 | spl4_46)),
% 1.68/0.60    inference(forward_demodulation,[],[f1513,f30])).
% 1.68/0.60  fof(f1513,plain,(
% 1.68/0.60    ~r1_tarski(sK3,k2_xboole_0(sK1,sK0)) | (~spl4_20 | spl4_46)),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f1121,f622])).
% 1.68/0.60  fof(f622,plain,(
% 1.68/0.60    ( ! [X0] : (~r1_tarski(sK3,k2_xboole_0(sK1,X0)) | r1_tarski(sK3,X0)) ) | ~spl4_20),
% 1.68/0.60    inference(superposition,[],[f37,f238])).
% 1.68/0.60  fof(f238,plain,(
% 1.68/0.60    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_20),
% 1.68/0.60    inference(avatar_component_clause,[],[f236])).
% 1.68/0.60  fof(f236,plain,(
% 1.68/0.60    spl4_20 <=> sK3 = k4_xboole_0(sK3,sK1)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.68/0.60  fof(f1121,plain,(
% 1.68/0.60    ~r1_tarski(sK3,sK0) | spl4_46),
% 1.68/0.60    inference(avatar_component_clause,[],[f1119])).
% 1.68/0.60  fof(f1119,plain,(
% 1.68/0.60    spl4_46 <=> r1_tarski(sK3,sK0)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.68/0.60  fof(f1127,plain,(
% 1.68/0.60    ~spl4_46 | spl4_47 | ~spl4_30),
% 1.68/0.60    inference(avatar_split_clause,[],[f1115,f436,f1123,f1119])).
% 1.68/0.60  fof(f1115,plain,(
% 1.68/0.60    sK0 = sK3 | ~r1_tarski(sK3,sK0) | ~spl4_30),
% 1.68/0.60    inference(superposition,[],[f34,f696])).
% 1.68/0.60  fof(f696,plain,(
% 1.68/0.60    sK3 = k2_xboole_0(sK3,sK0) | ~spl4_30),
% 1.68/0.60    inference(backward_demodulation,[],[f398,f438])).
% 1.68/0.60  fof(f398,plain,(
% 1.68/0.60    sK3 = k2_xboole_0(sK3,k4_xboole_0(sK0,sK2))),
% 1.68/0.60    inference(superposition,[],[f164,f30])).
% 1.68/0.60  fof(f164,plain,(
% 1.68/0.60    sK3 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK3)),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f126,f34])).
% 1.68/0.60  fof(f126,plain,(
% 1.68/0.60    r1_tarski(k4_xboole_0(sK0,sK2),sK3)),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f28,f48])).
% 1.68/0.60  fof(f48,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,sK2),sK3) | ~r1_tarski(X1,k2_xboole_0(sK0,sK1))) )),
% 1.68/0.60    inference(superposition,[],[f37,f23])).
% 1.68/0.60  fof(f665,plain,(
% 1.68/0.60    spl4_32 | ~spl4_16),
% 1.68/0.60    inference(avatar_split_clause,[],[f652,f203,f458])).
% 1.68/0.60  fof(f652,plain,(
% 1.68/0.60    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_16),
% 1.68/0.60    inference(superposition,[],[f210,f603])).
% 1.68/0.60  fof(f603,plain,(
% 1.68/0.60    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl4_16),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f568,f34])).
% 1.68/0.60  fof(f568,plain,(
% 1.68/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_16),
% 1.68/0.60    inference(subsumption_resolution,[],[f532,f28])).
% 1.68/0.60  fof(f532,plain,(
% 1.68/0.60    ( ! [X0] : (~r1_tarski(sK2,k2_xboole_0(sK2,X0)) | r1_tarski(k1_xboole_0,X0)) ) | ~spl4_16),
% 1.68/0.60    inference(backward_demodulation,[],[f77,f205])).
% 1.68/0.60  fof(f77,plain,(
% 1.68/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~r1_tarski(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0))) )),
% 1.68/0.60    inference(superposition,[],[f37,f41])).
% 1.68/0.60  fof(f41,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f24,f40])).
% 1.68/0.60  fof(f24,plain,(
% 1.68/0.60    r1_xboole_0(sK2,sK0)),
% 1.68/0.60    inference(cnf_transformation,[],[f22])).
% 1.68/0.60  fof(f210,plain,(
% 1.68/0.60    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 1.68/0.60    inference(superposition,[],[f39,f91])).
% 1.68/0.60  fof(f664,plain,(
% 1.68/0.60    spl4_30 | ~spl4_16),
% 1.68/0.60    inference(avatar_split_clause,[],[f651,f203,f436])).
% 1.68/0.60  fof(f651,plain,(
% 1.68/0.60    sK0 = k4_xboole_0(sK0,sK2) | ~spl4_16),
% 1.68/0.60    inference(superposition,[],[f177,f603])).
% 1.68/0.60  fof(f177,plain,(
% 1.68/0.60    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 1.68/0.60    inference(superposition,[],[f39,f72])).
% 1.68/0.60  fof(f72,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.68/0.60    inference(superposition,[],[f41,f38])).
% 1.68/0.60  fof(f570,plain,(
% 1.68/0.60    ~spl4_16 | spl4_19),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f569])).
% 1.68/0.60  fof(f569,plain,(
% 1.68/0.60    $false | (~spl4_16 | spl4_19)),
% 1.68/0.60    inference(subsumption_resolution,[],[f539,f28])).
% 1.68/0.60  fof(f539,plain,(
% 1.68/0.60    ~r1_tarski(sK2,k2_xboole_0(sK2,k4_xboole_0(sK3,sK1))) | (~spl4_16 | spl4_19)),
% 1.68/0.60    inference(backward_demodulation,[],[f361,f205])).
% 1.68/0.60  fof(f361,plain,(
% 1.68/0.60    ~r1_tarski(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK3,sK1))) | spl4_19),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f234,f77])).
% 1.68/0.60  fof(f234,plain,(
% 1.68/0.60    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK3,sK1)) | spl4_19),
% 1.68/0.60    inference(avatar_component_clause,[],[f232])).
% 1.68/0.60  fof(f232,plain,(
% 1.68/0.60    spl4_19 <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.68/0.60  fof(f528,plain,(
% 1.68/0.60    spl4_15),
% 1.68/0.60    inference(avatar_split_clause,[],[f520,f199])).
% 1.68/0.60  fof(f199,plain,(
% 1.68/0.60    spl4_15 <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.68/0.60  fof(f520,plain,(
% 1.68/0.60    r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f193,f209])).
% 1.68/0.60  fof(f209,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(X1,k4_xboole_0(sK2,sK0)) | ~r1_tarski(X1,sK2)) )),
% 1.68/0.60    inference(forward_demodulation,[],[f197,f27])).
% 1.68/0.60  fof(f197,plain,(
% 1.68/0.60    ( ! [X1] : (~r1_tarski(X1,sK2) | r1_tarski(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(sK2,sK0))) )),
% 1.68/0.60    inference(superposition,[],[f37,f74])).
% 1.68/0.60  fof(f74,plain,(
% 1.68/0.60    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.68/0.60    inference(superposition,[],[f39,f41])).
% 1.68/0.60  fof(f193,plain,(
% 1.68/0.60    r1_tarski(k1_xboole_0,sK2)),
% 1.68/0.60    inference(superposition,[],[f28,f74])).
% 1.68/0.60  fof(f241,plain,(
% 1.68/0.60    ~spl4_19 | spl4_20),
% 1.68/0.60    inference(avatar_split_clause,[],[f228,f236,f232])).
% 1.68/0.60  fof(f228,plain,(
% 1.68/0.60    sK3 = k4_xboole_0(sK3,sK1) | ~r1_tarski(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 1.68/0.60    inference(superposition,[],[f34,f93])).
% 1.68/0.60  fof(f93,plain,(
% 1.68/0.60    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 1.68/0.60    inference(superposition,[],[f39,f42])).
% 1.68/0.60  fof(f208,plain,(
% 1.68/0.60    ~spl4_15 | spl4_16),
% 1.68/0.60    inference(avatar_split_clause,[],[f195,f203,f199])).
% 1.68/0.60  fof(f195,plain,(
% 1.68/0.60    sK2 = k4_xboole_0(sK2,sK0) | ~r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.68/0.60    inference(superposition,[],[f34,f74])).
% 1.68/0.60  % SZS output end Proof for theBenchmark
% 1.68/0.60  % (24567)------------------------------
% 1.68/0.60  % (24567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (24567)Termination reason: Refutation
% 1.68/0.60  
% 1.68/0.60  % (24567)Memory used [KB]: 11641
% 1.68/0.60  % (24567)Time elapsed: 0.203 s
% 1.68/0.60  % (24567)------------------------------
% 1.68/0.60  % (24567)------------------------------
% 1.68/0.60  % (24540)Success in time 0.243 s
%------------------------------------------------------------------------------
