%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 363 expanded)
%              Number of leaves         :   23 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  226 ( 762 expanded)
%              Number of equality atoms :   13 (  53 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f54,f59,f64,f79,f99,f104,f181,f186,f322,f387,f392,f1128,f1133,f1223,f1235,f1237])).

fof(f1237,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f1236])).

fof(f1236,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(subsumption_resolution,[],[f1211,f78])).

fof(f78,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_6
  <=> r1_tarski(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1211,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f1036,f53])).

fof(f53,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_3
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1036,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f935,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f935,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK2),X0),sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f572,f73])).

fof(f73,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | r1_tarski(X1,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f572,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) ),
    inference(unit_resulting_resolution,[],[f507,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f507,plain,(
    ! [X6] : r1_tarski(X6,X6) ),
    inference(superposition,[],[f444,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f444,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f23,f29])).

fof(f1235,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f1234])).

fof(f1234,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_11 ),
    inference(subsumption_resolution,[],[f1233,f444])).

fof(f1233,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k3_xboole_0(sK0,sK2),sK1))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_11 ),
    inference(forward_demodulation,[],[f1183,f53])).

fof(f1183,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1))
    | ~ spl3_2
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f321,f1036,f30])).

fof(f321,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl3_11
  <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f1223,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f1222])).

fof(f1222,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(subsumption_resolution,[],[f1221,f507])).

fof(f1221,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(forward_demodulation,[],[f1193,f53])).

fof(f1193,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl3_2
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f78,f1036,f30])).

fof(f1133,plain,
    ( spl3_15
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1120,f35,f1130])).

fof(f1130,plain,
    ( spl3_15
  <=> r1_tarski(k2_xboole_0(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f35,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1120,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK0),sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f1011,f571])).

fof(f571,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f507,f27])).

fof(f1011,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(X0,sK0),k2_xboole_0(X0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f932,f29])).

fof(f932,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK0),X0),sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f572,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_1 ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f1128,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1113,f56,f35,f1125])).

fof(f1125,plain,
    ( spl3_14
  <=> r1_tarski(k2_xboole_0(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f56,plain,
    ( spl3_4
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1113,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK0),sK1)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f1011,f58])).

fof(f58,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f392,plain,
    ( ~ spl3_13
    | spl3_10 ),
    inference(avatar_split_clause,[],[f259,f183,f389])).

fof(f389,plain,
    ( spl3_13
  <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f183,plain,
    ( spl3_10
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f259,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK2))
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f185,f28])).

fof(f185,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f387,plain,
    ( ~ spl3_12
    | spl3_9 ),
    inference(avatar_split_clause,[],[f257,f178,f384])).

fof(f384,plain,
    ( spl3_12
  <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f178,plain,
    ( spl3_9
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f257,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK0))
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f180,f28])).

fof(f180,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f178])).

fof(f322,plain,
    ( ~ spl3_11
    | spl3_5 ),
    inference(avatar_split_clause,[],[f258,f61,f319])).

fof(f61,plain,
    ( spl3_5
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f258,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1))
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f63,f28])).

fof(f63,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f186,plain,
    ( ~ spl3_10
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f69,f61,f40,f183])).

fof(f69,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK2)
    | ~ spl3_2
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f63,f42,f30])).

fof(f181,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f67,f61,f35,f178])).

fof(f67,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK0)
    | ~ spl3_1
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f63,f37,f30])).

fof(f104,plain,
    ( ~ spl3_8
    | ~ spl3_2
    | spl3_6 ),
    inference(avatar_split_clause,[],[f91,f76,f40,f101])).

fof(f101,plain,
    ( spl3_8
  <=> r1_tarski(k2_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK2)
    | ~ spl3_2
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f42,f78,f30])).

fof(f99,plain,
    ( ~ spl3_7
    | ~ spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f90,f76,f35,f96])).

fof(f96,plain,
    ( spl3_7
  <=> r1_tarski(k2_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f90,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK0)
    | ~ spl3_1
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f37,f78,f30])).

fof(f79,plain,
    ( ~ spl3_6
    | spl3_5 ),
    inference(avatar_split_clause,[],[f65,f61,f76])).

fof(f65,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f23,f63,f30])).

fof(f64,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f22,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f59,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f40,f56])).

fof(f45,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f42,f27])).

fof(f54,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f44,f35,f51])).

fof(f44,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f37,f27])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:54:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (21296)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.46  % (21291)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (21304)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (21295)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (21288)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (21299)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (21290)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (21293)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (21292)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (21289)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (21294)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (21297)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (21306)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (21301)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (21300)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (21298)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (21296)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f1241,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f38,f43,f54,f59,f64,f79,f99,f104,f181,f186,f322,f387,f392,f1128,f1133,f1223,f1235,f1237])).
% 0.22/0.53  fof(f1237,plain,(
% 0.22/0.53    ~spl3_2 | ~spl3_3 | spl3_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f1236])).
% 0.22/0.53  fof(f1236,plain,(
% 0.22/0.53    $false | (~spl3_2 | ~spl3_3 | spl3_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f1211,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),sK1) | spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl3_6 <=> r1_tarski(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f1211,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(sK0,sK2),sK1) | (~spl3_2 | ~spl3_3)),
% 0.22/0.53    inference(superposition,[],[f1036,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl3_3 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f1036,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK1))) ) | ~spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f935,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.53  fof(f935,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK2),X0),sK1)) ) | ~spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f572,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(X1,sK2) | r1_tarski(X1,sK1)) ) | ~spl3_2),
% 0.22/0.53    inference(resolution,[],[f30,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.53  fof(f572,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1)) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f507,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.53  fof(f507,plain,(
% 0.22/0.53    ( ! [X6] : (r1_tarski(X6,X6)) )),
% 0.22/0.53    inference(superposition,[],[f444,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f23,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.53  fof(f444,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f23,f29])).
% 0.22/0.53  fof(f1235,plain,(
% 0.22/0.53    ~spl3_2 | ~spl3_3 | spl3_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f1234])).
% 0.22/0.53  fof(f1234,plain,(
% 0.22/0.53    $false | (~spl3_2 | ~spl3_3 | spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f1233,f444])).
% 0.22/0.53  fof(f1233,plain,(
% 0.22/0.53    ~r1_tarski(sK1,k2_xboole_0(k3_xboole_0(sK0,sK2),sK1)) | (~spl3_2 | ~spl3_3 | spl3_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f1183,f53])).
% 0.22/0.53  fof(f1183,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1)) | (~spl3_2 | spl3_11)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f321,f1036,f30])).
% 0.22/0.53  fof(f321,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1)) | spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f319])).
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    spl3_11 <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f1223,plain,(
% 0.22/0.53    ~spl3_2 | ~spl3_3 | spl3_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f1222])).
% 0.22/0.53  fof(f1222,plain,(
% 0.22/0.53    $false | (~spl3_2 | ~spl3_3 | spl3_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f1221,f507])).
% 0.22/0.53  fof(f1221,plain,(
% 0.22/0.53    ~r1_tarski(sK1,sK1) | (~spl3_2 | ~spl3_3 | spl3_6)),
% 0.22/0.53    inference(forward_demodulation,[],[f1193,f53])).
% 0.22/0.53  fof(f1193,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK1),sK1) | (~spl3_2 | spl3_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f78,f1036,f30])).
% 0.22/0.53  fof(f1133,plain,(
% 0.22/0.53    spl3_15 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f1120,f35,f1130])).
% 0.22/0.53  fof(f1130,plain,(
% 0.22/0.53    spl3_15 <=> r1_tarski(k2_xboole_0(sK1,sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f1120,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(sK1,sK0),sK1) | ~spl3_1),
% 0.22/0.53    inference(superposition,[],[f1011,f571])).
% 0.22/0.53  fof(f571,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f507,f27])).
% 0.22/0.53  fof(f1011,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK0),k2_xboole_0(X0,sK1))) ) | ~spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f932,f29])).
% 0.22/0.53  fof(f932,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK0),X0),sK1)) ) | ~spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f572,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) ) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f30,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f35])).
% 0.22/0.53  fof(f1128,plain,(
% 0.22/0.53    spl3_14 | ~spl3_1 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f1113,f56,f35,f1125])).
% 0.22/0.53  fof(f1125,plain,(
% 0.22/0.53    spl3_14 <=> r1_tarski(k2_xboole_0(sK2,sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl3_4 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f1113,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(sK2,sK0),sK1) | (~spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(superposition,[],[f1011,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f56])).
% 0.22/0.53  fof(f392,plain,(
% 0.22/0.53    ~spl3_13 | spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f259,f183,f389])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    spl3_13 <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    spl3_10 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK2)) | spl3_10),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f185,f28])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK2) | spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f183])).
% 0.22/0.53  fof(f387,plain,(
% 0.22/0.53    ~spl3_12 | spl3_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f257,f178,f384])).
% 0.22/0.53  fof(f384,plain,(
% 0.22/0.53    spl3_12 <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    spl3_9 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK0)) | spl3_9),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f180,f28])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK0) | spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f178])).
% 0.22/0.53  fof(f322,plain,(
% 0.22/0.53    ~spl3_11 | spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f258,f61,f319])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl3_5 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK2),sK1)) | spl3_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f63,f28])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1) | spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    ~spl3_10 | ~spl3_2 | spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f69,f61,f40,f183])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK2) | (~spl3_2 | spl3_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f63,f42,f30])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~spl3_9 | ~spl3_1 | spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f67,f61,f35,f178])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK0) | (~spl3_1 | spl3_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f63,f37,f30])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ~spl3_8 | ~spl3_2 | spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f91,f76,f40,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl3_8 <=> r1_tarski(k2_xboole_0(sK0,sK2),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),sK2) | (~spl3_2 | spl3_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f42,f78,f30])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~spl3_7 | ~spl3_1 | spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f90,f76,f35,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl3_7 <=> r1_tarski(k2_xboole_0(sK0,sK2),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),sK0) | (~spl3_1 | spl3_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f37,f78,f30])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ~spl3_6 | spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f65,f61,f76])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,sK2),sK1) | spl3_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f23,f63,f30])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f61])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f22,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl3_4 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f40,f56])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f42,f27])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    spl3_3 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f35,f51])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f37,f27])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f40])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    r1_tarski(sK2,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f35])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    r1_tarski(sK0,sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f19])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (21296)------------------------------
% 1.34/0.53  % (21296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (21296)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (21296)Memory used [KB]: 7036
% 1.34/0.53  % (21296)Time elapsed: 0.112 s
% 1.34/0.53  % (21296)------------------------------
% 1.34/0.53  % (21296)------------------------------
% 1.34/0.53  % (21305)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.34/0.53  % (21287)Success in time 0.167 s
%------------------------------------------------------------------------------
