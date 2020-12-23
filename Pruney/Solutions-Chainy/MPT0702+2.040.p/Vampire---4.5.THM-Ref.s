%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 220 expanded)
%              Number of leaves         :   30 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  306 ( 654 expanded)
%              Number of equality atoms :   66 ( 121 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1035,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f83,f148,f409,f420,f427,f435,f561,f621,f634,f946,f971,f983,f1029])).

fof(f1029,plain,
    ( spl3_1
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f1017,f964,f48])).

fof(f48,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f964,plain,
    ( spl3_49
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f1017,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_49 ),
    inference(trivial_inequality_removal,[],[f1008])).

fof(f1008,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl3_49 ),
    inference(superposition,[],[f43,f966])).

fof(f966,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f964])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f983,plain,
    ( ~ spl3_3
    | spl3_50 ),
    inference(avatar_contradiction_clause,[],[f980])).

fof(f980,plain,
    ( $false
    | ~ spl3_3
    | spl3_50 ),
    inference(resolution,[],[f970,f226])).

fof(f226,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK2))
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK2)) )
    | ~ spl3_3 ),
    inference(superposition,[],[f43,f220])).

fof(f220,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k1_relat_1(sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f150,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f150,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = k4_xboole_0(X2,k1_relat_1(sK2)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f60,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f970,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_relat_1(sK2))
    | spl3_50 ),
    inference(avatar_component_clause,[],[f968])).

fof(f968,plain,
    ( spl3_50
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f971,plain,
    ( spl3_49
    | ~ spl3_50
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f948,f943,f968,f964])).

fof(f943,plain,
    ( spl3_47
  <=> k1_relat_1(sK2) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f948,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_47 ),
    inference(superposition,[],[f40,f945])).

fof(f945,plain,
    ( k1_relat_1(sK2) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f943])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f946,plain,
    ( spl3_47
    | ~ spl3_24
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f941,f631,f432,f943])).

fof(f432,plain,
    ( spl3_24
  <=> k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f631,plain,
    ( spl3_41
  <=> k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f941,plain,
    ( k1_relat_1(sK2) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_24
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f434,f633])).

fof(f633,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f631])).

fof(f434,plain,
    ( k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f432])).

fof(f634,plain,
    ( spl3_41
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f629,f618,f631])).

fof(f618,plain,
    ( spl3_40
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f629,plain,
    ( k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f627,f34])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f627,plain,
    ( k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) = k4_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_40 ),
    inference(superposition,[],[f37,f620])).

fof(f620,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f618])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f621,plain,
    ( spl3_40
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f610,f559,f618])).

fof(f559,plain,
    ( spl3_36
  <=> ! [X9] : r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f610,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_36 ),
    inference(superposition,[],[f601,f34])).

fof(f601,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(X1,X1))
    | ~ spl3_36 ),
    inference(resolution,[],[f560,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f560,plain,
    ( ! [X9] : r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f559])).

fof(f561,plain,
    ( ~ spl3_6
    | spl3_36
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f546,f81,f559,f73])).

fof(f73,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,
    ( spl3_7
  <=> ! [X1,X0] : k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f546,plain,
    ( ! [X9] :
        ( r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f545])).

fof(f545,plain,
    ( ! [X9] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(superposition,[],[f38,f519])).

fof(f519,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(X0,X0))
    | ~ spl3_7 ),
    inference(superposition,[],[f471,f82])).

fof(f82,plain,
    ( ! [X0,X1] : k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f471,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,X3),k9_relat_1(sK2,X3))
    | ~ spl3_7 ),
    inference(resolution,[],[f440,f44])).

fof(f440,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0))
    | ~ spl3_7 ),
    inference(superposition,[],[f403,f34])).

fof(f403,plain,
    ( ! [X19,X18] : r1_tarski(k9_relat_1(sK2,k4_xboole_0(X18,X19)),k9_relat_1(sK2,X18))
    | ~ spl3_7 ),
    inference(superposition,[],[f35,f82])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f435,plain,
    ( spl3_24
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f429,f424,f432])).

fof(f424,plain,
    ( spl3_23
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f429,plain,
    ( k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_23 ),
    inference(superposition,[],[f37,f426])).

fof(f426,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f424])).

fof(f427,plain,
    ( spl3_23
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f422,f417,f424])).

fof(f417,plain,
    ( spl3_22
  <=> r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f422,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_22 ),
    inference(resolution,[],[f419,f41])).

fof(f419,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f417])).

fof(f420,plain,
    ( ~ spl3_6
    | spl3_22
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f413,f405,f417,f73])).

fof(f405,plain,
    ( spl3_21
  <=> k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f413,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(superposition,[],[f38,f407])).

fof(f407,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f405])).

fof(f409,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f393,f145,f81,f405])).

fof(f145,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f393,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(superposition,[],[f147,f82])).

fof(f147,plain,
    ( k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f143,f63,f145])).

fof(f63,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f143,plain,
    ( k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f65,f44])).

fof(f65,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f83,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f79,f53,f81,f68,f73])).

fof(f68,plain,
    ( spl3_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f53,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f78,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f77,f36])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f55,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f76,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f58])).

fof(f30,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f48])).

fof(f32,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:50:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.45  % (8868)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (8869)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (8867)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (8871)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (8866)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (8877)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (8865)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (8874)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (8870)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (8863)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (8864)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (8875)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (8874)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1035,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f83,f148,f409,f420,f427,f435,f561,f621,f634,f946,f971,f983,f1029])).
% 0.22/0.52  fof(f1029,plain,(
% 0.22/0.52    spl3_1 | ~spl3_49),
% 0.22/0.52    inference(avatar_split_clause,[],[f1017,f964,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f964,plain,(
% 0.22/0.52    spl3_49 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.52  fof(f1017,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | ~spl3_49),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f1008])).
% 0.22/0.52  fof(f1008,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl3_49),
% 0.22/0.52    inference(superposition,[],[f43,f966])).
% 0.22/0.52  fof(f966,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_49),
% 0.22/0.52    inference(avatar_component_clause,[],[f964])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.52  fof(f983,plain,(
% 0.22/0.52    ~spl3_3 | spl3_50),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f980])).
% 0.22/0.52  fof(f980,plain,(
% 0.22/0.52    $false | (~spl3_3 | spl3_50)),
% 0.22/0.52    inference(resolution,[],[f970,f226])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK2))) ) | ~spl3_3),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f223])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK2))) ) | ~spl3_3),
% 0.22/0.52    inference(superposition,[],[f43,f220])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k1_relat_1(sK2))) ) | ~spl3_3),
% 0.22/0.52    inference(resolution,[],[f150,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_xboole_0 = k4_xboole_0(X2,k1_relat_1(sK2))) ) | ~spl3_3),
% 0.22/0.52    inference(resolution,[],[f84,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(X0,sK0)) ) | ~spl3_3),
% 0.22/0.52    inference(resolution,[],[f60,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl3_3 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f970,plain,(
% 0.22/0.52    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_relat_1(sK2)) | spl3_50),
% 0.22/0.52    inference(avatar_component_clause,[],[f968])).
% 0.22/0.52  fof(f968,plain,(
% 0.22/0.52    spl3_50 <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.52  fof(f971,plain,(
% 0.22/0.52    spl3_49 | ~spl3_50 | ~spl3_47),
% 0.22/0.52    inference(avatar_split_clause,[],[f948,f943,f968,f964])).
% 0.22/0.52  fof(f943,plain,(
% 0.22/0.52    spl3_47 <=> k1_relat_1(sK2) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.52  fof(f948,plain,(
% 0.22/0.52    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_relat_1(sK2)) | k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_47),
% 0.22/0.52    inference(superposition,[],[f40,f945])).
% 0.22/0.52  fof(f945,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~spl3_47),
% 0.22/0.52    inference(avatar_component_clause,[],[f943])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.22/0.52  fof(f946,plain,(
% 0.22/0.52    spl3_47 | ~spl3_24 | ~spl3_41),
% 0.22/0.52    inference(avatar_split_clause,[],[f941,f631,f432,f943])).
% 0.22/0.52  fof(f432,plain,(
% 0.22/0.52    spl3_24 <=> k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.52  fof(f631,plain,(
% 0.22/0.52    spl3_41 <=> k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.52  fof(f941,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) | (~spl3_24 | ~spl3_41)),
% 0.22/0.52    inference(forward_demodulation,[],[f434,f633])).
% 0.22/0.52  fof(f633,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) | ~spl3_41),
% 0.22/0.52    inference(avatar_component_clause,[],[f631])).
% 0.22/0.52  fof(f434,plain,(
% 0.22/0.52    k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) | ~spl3_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f432])).
% 0.22/0.52  fof(f634,plain,(
% 0.22/0.52    spl3_41 | ~spl3_40),
% 0.22/0.52    inference(avatar_split_clause,[],[f629,f618,f631])).
% 0.22/0.52  fof(f618,plain,(
% 0.22/0.52    spl3_40 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.52  fof(f629,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) | ~spl3_40),
% 0.22/0.52    inference(forward_demodulation,[],[f627,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f627,plain,(
% 0.22/0.52    k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) = k4_xboole_0(k1_relat_1(sK2),k1_xboole_0) | ~spl3_40),
% 0.22/0.52    inference(superposition,[],[f37,f620])).
% 0.22/0.52  fof(f620,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k1_xboole_0) | ~spl3_40),
% 0.22/0.52    inference(avatar_component_clause,[],[f618])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f621,plain,(
% 0.22/0.52    spl3_40 | ~spl3_36),
% 0.22/0.52    inference(avatar_split_clause,[],[f610,f559,f618])).
% 0.22/0.52  fof(f559,plain,(
% 0.22/0.52    spl3_36 <=> ! [X9] : r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.52  fof(f610,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k1_xboole_0) | ~spl3_36),
% 0.22/0.52    inference(superposition,[],[f601,f34])).
% 0.22/0.52  fof(f601,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(X1,X1))) ) | ~spl3_36),
% 0.22/0.52    inference(resolution,[],[f560,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.52  fof(f560,plain,(
% 0.22/0.52    ( ! [X9] : (r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9))) ) | ~spl3_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f559])).
% 0.22/0.52  fof(f561,plain,(
% 0.22/0.52    ~spl3_6 | spl3_36 | ~spl3_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f546,f81,f559,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl3_6 <=> v1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl3_7 <=> ! [X1,X0] : k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f546,plain,(
% 0.22/0.52    ( ! [X9] : (r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9)) | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f545])).
% 0.22/0.52  fof(f545,plain,(
% 0.22/0.52    ( ! [X9] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(X9,X9)) | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 0.22/0.52    inference(superposition,[],[f38,f519])).
% 0.22/0.52  fof(f519,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(X0,X0))) ) | ~spl3_7),
% 0.22/0.52    inference(superposition,[],[f471,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f471,plain,(
% 0.22/0.52    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,X3),k9_relat_1(sK2,X3))) ) | ~spl3_7),
% 0.22/0.52    inference(resolution,[],[f440,f44])).
% 0.22/0.52  fof(f440,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0))) ) | ~spl3_7),
% 0.22/0.52    inference(superposition,[],[f403,f34])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    ( ! [X19,X18] : (r1_tarski(k9_relat_1(sK2,k4_xboole_0(X18,X19)),k9_relat_1(sK2,X18))) ) | ~spl3_7),
% 0.22/0.52    inference(superposition,[],[f35,f82])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.22/0.52  fof(f435,plain,(
% 0.22/0.52    spl3_24 | ~spl3_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f429,f424,f432])).
% 0.22/0.52  fof(f424,plain,(
% 0.22/0.52    spl3_23 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.52  fof(f429,plain,(
% 0.22/0.52    k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) | ~spl3_23),
% 0.22/0.52    inference(superposition,[],[f37,f426])).
% 0.22/0.52  fof(f426,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~spl3_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f424])).
% 0.22/0.52  fof(f427,plain,(
% 0.22/0.52    spl3_23 | ~spl3_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f422,f417,f424])).
% 0.22/0.52  fof(f417,plain,(
% 0.22/0.52    spl3_22 <=> r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.52  fof(f422,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~spl3_22),
% 0.22/0.52    inference(resolution,[],[f419,f41])).
% 0.22/0.52  fof(f419,plain,(
% 0.22/0.52    r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~spl3_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f417])).
% 0.22/0.52  fof(f420,plain,(
% 0.22/0.52    ~spl3_6 | spl3_22 | ~spl3_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f413,f405,f417,f73])).
% 0.22/0.52  fof(f405,plain,(
% 0.22/0.52    spl3_21 <=> k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f413,plain,(
% 0.22/0.52    r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~v1_relat_1(sK2) | ~spl3_21),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f412])).
% 0.22/0.52  fof(f412,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~v1_relat_1(sK2) | ~spl3_21),
% 0.22/0.52    inference(superposition,[],[f38,f407])).
% 0.22/0.52  fof(f407,plain,(
% 0.22/0.52    k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f405])).
% 0.22/0.52  fof(f409,plain,(
% 0.22/0.52    spl3_21 | ~spl3_7 | ~spl3_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f393,f145,f81,f405])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    spl3_16 <=> k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.52  fof(f393,plain,(
% 0.22/0.52    k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_16)),
% 0.22/0.52    inference(superposition,[],[f147,f82])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | ~spl3_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f145])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl3_16 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f143,f63,f145])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl3_4 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f65,f44])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f63])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~spl3_6 | ~spl3_5 | spl3_7 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f79,f53,f81,f68,f73])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl3_5 <=> v1_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_2),
% 0.22/0.52    inference(forward_demodulation,[],[f78,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_2),
% 0.22/0.52    inference(forward_demodulation,[],[f77,f36])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f55,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f53])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f73])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f68])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f63])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f58])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f31,f53])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ~spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f32,f48])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ~r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (8874)------------------------------
% 0.22/0.52  % (8874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8874)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (8874)Memory used [KB]: 11129
% 0.22/0.52  % (8874)Time elapsed: 0.092 s
% 0.22/0.52  % (8874)------------------------------
% 0.22/0.52  % (8874)------------------------------
% 0.22/0.52  % (8876)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (8879)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (8878)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.53  % (8880)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.53  % (8873)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (8862)Success in time 0.161 s
%------------------------------------------------------------------------------
