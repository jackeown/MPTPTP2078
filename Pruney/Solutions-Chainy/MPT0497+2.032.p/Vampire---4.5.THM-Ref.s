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
% DateTime   : Thu Dec  3 12:48:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 160 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 367 expanded)
%              Number of equality atoms :   64 ( 115 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f74,f81,f103,f175,f295,f313,f330,f334,f351])).

fof(f351,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(global_subsumption,[],[f28,f73,f345])).

fof(f345,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(resolution,[],[f80,f174])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl2_17
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | ~ r1_xboole_0(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f80,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_6
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f73,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f28,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f334,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl2_5
    | ~ spl2_6 ),
    inference(global_subsumption,[],[f80,f156])).

fof(f156,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f72,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f72,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f330,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | spl2_6
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | spl2_6
    | ~ spl2_23 ),
    inference(global_subsumption,[],[f79,f328])).

fof(f328,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f327,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f327,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f324,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f324,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(superposition,[],[f312,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_4
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f312,plain,
    ( ! [X4] : r1_xboole_0(X4,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4))))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl2_23
  <=> ! [X4] : r1_xboole_0(X4,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f79,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f313,plain,
    ( spl2_23
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f302,f293,f311])).

fof(f293,plain,
    ( spl2_22
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f302,plain,
    ( ! [X4] : r1_xboole_0(X4,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4))))
    | ~ spl2_22 ),
    inference(superposition,[],[f85,f294])).

fof(f294,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f293])).

fof(f85,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) ),
    inference(unit_resulting_resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f295,plain,
    ( spl2_22
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f210,f52,f293])).

fof(f52,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f210,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f54,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f54,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f175,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f148,f101,f52,f173])).

fof(f101,plain,
    ( spl2_7
  <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f148,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,X0)
        | ~ r1_xboole_0(X0,k1_relat_1(sK1)) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f145,f102])).

fof(f102,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k5_relat_1(k6_relat_1(X0),sK1) )
    | ~ spl2_1 ),
    inference(resolution,[],[f106,f54])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X1,k1_relat_1(X2))
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f105,f35])).

fof(f35,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(k2_relat_1(k6_relat_1(X1)),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

fof(f103,plain,
    ( spl2_7
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f96,f52,f101])).

fof(f96,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f54,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f81,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f75,f71,f78])).

fof(f75,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f73,f43])).

fof(f74,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f27,f71,f67])).

fof(f27,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f55,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (14756)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.43  % (14756)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f352,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f55,f60,f74,f81,f103,f175,f295,f313,f330,f334,f351])).
% 0.20/0.43  fof(f351,plain,(
% 0.20/0.43    ~spl2_5 | ~spl2_6 | ~spl2_17),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f350])).
% 0.20/0.43  fof(f350,plain,(
% 0.20/0.43    $false | (~spl2_5 | ~spl2_6 | ~spl2_17)),
% 0.20/0.43    inference(global_subsumption,[],[f28,f73,f345])).
% 0.20/0.43  fof(f345,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_6 | ~spl2_17)),
% 0.20/0.43    inference(resolution,[],[f80,f174])).
% 0.20/0.43  fof(f174,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | ~spl2_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f173])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    spl2_17 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,X0) | ~r1_xboole_0(X0,k1_relat_1(sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f78])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    spl2_6 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl2_5 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.43    inference(negated_conjecture,[],[f14])).
% 0.20/0.43  fof(f14,conjecture,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.43  fof(f334,plain,(
% 0.20/0.43    spl2_5 | ~spl2_6),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f333])).
% 0.20/0.43  fof(f333,plain,(
% 0.20/0.43    $false | (spl2_5 | ~spl2_6)),
% 0.20/0.43    inference(global_subsumption,[],[f80,f156])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k1_relat_1(sK1)) | spl2_5),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f72,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f330,plain,(
% 0.20/0.43    ~spl2_2 | ~spl2_4 | spl2_6 | ~spl2_23),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f329])).
% 0.20/0.43  fof(f329,plain,(
% 0.20/0.43    $false | (~spl2_2 | ~spl2_4 | spl2_6 | ~spl2_23)),
% 0.20/0.43    inference(global_subsumption,[],[f79,f328])).
% 0.20/0.43  fof(f328,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k1_relat_1(sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 0.20/0.43    inference(forward_demodulation,[],[f327,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(forward_demodulation,[],[f47,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f32,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f38,f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f33,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f40,f44])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.43  fof(f327,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_xboole_0)) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 0.20/0.43    inference(forward_demodulation,[],[f324,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl2_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f324,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k1_xboole_0))) | (~spl2_4 | ~spl2_23)),
% 0.20/0.43    inference(superposition,[],[f312,f69])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl2_4 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f312,plain,(
% 0.20/0.43    ( ! [X4] : (r1_xboole_0(X4,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4))))) ) | ~spl2_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f311])).
% 0.20/0.43  fof(f311,plain,(
% 0.20/0.43    spl2_23 <=> ! [X4] : r1_xboole_0(X4,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k1_relat_1(sK1)) | spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f78])).
% 0.20/0.43  fof(f313,plain,(
% 0.20/0.43    spl2_23 | ~spl2_22),
% 0.20/0.43    inference(avatar_split_clause,[],[f302,f293,f311])).
% 0.20/0.43  fof(f293,plain,(
% 0.20/0.43    spl2_22 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.43  fof(f302,plain,(
% 0.20/0.43    ( ! [X4] : (r1_xboole_0(X4,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4))))) ) | ~spl2_22),
% 0.20/0.43    inference(superposition,[],[f85,f294])).
% 0.20/0.43  fof(f294,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) ) | ~spl2_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f293])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) )),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f48,f43])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f37,f45])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.43  fof(f295,plain,(
% 0.20/0.43    spl2_22 | ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f210,f52,f293])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f210,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) ) | ~spl2_1),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f54,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f42,f44])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f52])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    spl2_17 | ~spl2_1 | ~spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f148,f101,f52,f173])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    spl2_7 <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,X0) | ~r1_xboole_0(X0,k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_7)),
% 0.20/0.43    inference(forward_demodulation,[],[f145,f102])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f101])).
% 0.20/0.43  fof(f145,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_1),
% 0.20/0.43    inference(resolution,[],[f106,f54])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    ( ! [X2,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X1,k1_relat_1(X2)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f105,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    ( ! [X2,X1] : (~r1_xboole_0(k2_relat_1(k6_relat_1(X1)),k1_relat_1(X2)) | ~v1_relat_1(X2) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)) )),
% 0.20/0.43    inference(resolution,[],[f36,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_xboole_0 = k5_relat_1(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(flattening,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) => k1_xboole_0 = k5_relat_1(X0,X1))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    spl2_7 | ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f96,f52,f101])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_1),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f54,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl2_6 | ~spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f75,f71,f78])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_5),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f73,f43])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl2_4 | spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f71,f67])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f57])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f52])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    v1_relat_1(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (14756)------------------------------
% 0.20/0.43  % (14756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (14756)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (14756)Memory used [KB]: 10874
% 0.20/0.43  % (14756)Time elapsed: 0.015 s
% 0.20/0.43  % (14756)------------------------------
% 0.20/0.43  % (14756)------------------------------
% 0.20/0.43  % (14738)Success in time 0.075 s
%------------------------------------------------------------------------------
