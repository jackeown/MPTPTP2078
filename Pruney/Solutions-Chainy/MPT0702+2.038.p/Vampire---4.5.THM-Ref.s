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
% Statistics : Number of formulae       :  100 ( 175 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  271 ( 586 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f470,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f96,f115,f135,f157,f175,f179,f253,f374,f432,f469])).

fof(f469,plain,
    ( spl3_4
    | ~ spl3_21
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl3_4
    | ~ spl3_21
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f464,f57])).

fof(f57,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f464,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_21
    | ~ spl3_41 ),
    inference(superposition,[],[f431,f178])).

fof(f178,plain,
    ( ! [X1] : k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X1)),X1) = X1
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_21
  <=> ! [X1] : k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X1)),X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f431,plain,
    ( ! [X1] : r1_tarski(sK0,k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl3_41
  <=> ! [X1] : r1_tarski(sK0,k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f432,plain,
    ( spl3_41
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f403,f371,f430])).

fof(f371,plain,
    ( spl3_37
  <=> k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f403,plain,
    ( ! [X1] : r1_tarski(sK0,k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1))
    | ~ spl3_37 ),
    inference(superposition,[],[f79,f373])).

fof(f373,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f371])).

fof(f79,plain,(
    ! [X6,X4,X5] : r1_tarski(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6)) ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f374,plain,
    ( spl3_37
    | ~ spl3_6
    | ~ spl3_20
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f271,f251,f172,f65,f371])).

fof(f65,plain,
    ( spl3_6
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f172,plain,
    ( spl3_20
  <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f251,plain,
    ( spl3_29
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f271,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ spl3_6
    | ~ spl3_20
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f266,f174])).

fof(f174,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f172])).

fof(f266,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ spl3_6
    | ~ spl3_29 ),
    inference(resolution,[],[f252,f67])).

fof(f67,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f252,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f251])).

% (7844)Refutation not found, incomplete strategy% (7844)------------------------------
% (7844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7844)Termination reason: Refutation not found, incomplete strategy

% (7844)Memory used [KB]: 10490
% (7844)Time elapsed: 0.126 s
% (7844)------------------------------
% (7844)------------------------------
fof(f253,plain,
    ( spl3_29
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f119,f113,f251])).

fof(f113,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f119,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)) )
    | ~ spl3_12 ),
    inference(resolution,[],[f114,f30])).

fof(f30,plain,(
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

fof(f114,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f179,plain,
    ( spl3_21
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f98,f94,f177])).

fof(f94,plain,
    ( spl3_8
  <=> ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f98,plain,
    ( ! [X1] : k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X1)),X1) = X1
    | ~ spl3_8 ),
    inference(resolution,[],[f95,f30])).

fof(f95,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f175,plain,
    ( spl3_20
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f169,f154,f94,f172])).

fof(f154,plain,
    ( spl3_17
  <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f169,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f167,f95])).

fof(f167,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_17 ),
    inference(resolution,[],[f156,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f156,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f157,plain,
    ( spl3_17
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f152,f133,f60,f154])).

fof(f60,plain,
    ( spl3_5
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f133,plain,
    ( spl3_15
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f152,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f134,f62])).

fof(f62,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl3_15
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f87,f40,f133])).

fof(f40,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f115,plain,
    ( spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f81,f40,f113])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f42])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f96,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f92,f50,f45,f40,f94])).

fof(f45,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f90,f47])).

fof(f47,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f90,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f31,f52])).

fof(f52,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f68,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).

fof(f19,plain,
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

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f63,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (7843)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (7839)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (7863)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (7856)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (7841)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (7854)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (7840)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (7842)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (7847)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (7862)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (7838)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (7849)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (7839)Refutation not found, incomplete strategy% (7839)------------------------------
% 0.22/0.52  % (7839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7845)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (7851)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (7848)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (7855)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (7860)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (7857)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (7864)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (7859)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (7846)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (7850)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (7839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7839)Memory used [KB]: 10618
% 0.22/0.53  % (7839)Time elapsed: 0.105 s
% 0.22/0.53  % (7839)------------------------------
% 0.22/0.53  % (7839)------------------------------
% 0.22/0.53  % (7840)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (7858)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (7844)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (7853)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f470,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f96,f115,f135,f157,f175,f179,f253,f374,f432,f469])).
% 0.22/0.54  fof(f469,plain,(
% 0.22/0.54    spl3_4 | ~spl3_21 | ~spl3_41),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f468])).
% 0.22/0.54  fof(f468,plain,(
% 0.22/0.54    $false | (spl3_4 | ~spl3_21 | ~spl3_41)),
% 0.22/0.54    inference(subsumption_resolution,[],[f464,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK1) | spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f464,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | (~spl3_21 | ~spl3_41)),
% 0.22/0.54    inference(superposition,[],[f431,f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ( ! [X1] : (k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X1)),X1) = X1) ) | ~spl3_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f177])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    spl3_21 <=> ! [X1] : k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X1)),X1) = X1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.54  fof(f431,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(sK0,k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1))) ) | ~spl3_41),
% 0.22/0.54    inference(avatar_component_clause,[],[f430])).
% 0.22/0.54  fof(f430,plain,(
% 0.22/0.54    spl3_41 <=> ! [X1] : r1_tarski(sK0,k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.54  fof(f432,plain,(
% 0.22/0.54    spl3_41 | ~spl3_37),
% 0.22/0.54    inference(avatar_split_clause,[],[f403,f371,f430])).
% 0.22/0.54  fof(f371,plain,(
% 0.22/0.54    spl3_37 <=> k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.54  fof(f403,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(sK0,k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),X1))) ) | ~spl3_37),
% 0.22/0.54    inference(superposition,[],[f79,f373])).
% 0.22/0.54  fof(f373,plain,(
% 0.22/0.54    k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | ~spl3_37),
% 0.22/0.54    inference(avatar_component_clause,[],[f371])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X6,X4,X5] : (r1_tarski(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))) )),
% 0.22/0.54    inference(resolution,[],[f72,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(resolution,[],[f36,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f374,plain,(
% 0.22/0.54    spl3_37 | ~spl3_6 | ~spl3_20 | ~spl3_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f271,f251,f172,f65,f371])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    spl3_6 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    spl3_20 <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    spl3_29 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.54  fof(f271,plain,(
% 0.22/0.54    k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | (~spl3_6 | ~spl3_20 | ~spl3_29)),
% 0.22/0.54    inference(forward_demodulation,[],[f266,f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f172])).
% 0.22/0.54  fof(f266,plain,(
% 0.22/0.54    k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | (~spl3_6 | ~spl3_29)),
% 0.22/0.54    inference(resolution,[],[f252,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | ~spl3_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f65])).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3))) ) | ~spl3_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f251])).
% 0.22/0.54  % (7844)Refutation not found, incomplete strategy% (7844)------------------------------
% 0.22/0.54  % (7844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7844)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7844)Memory used [KB]: 10490
% 0.22/0.54  % (7844)Time elapsed: 0.126 s
% 0.22/0.54  % (7844)------------------------------
% 0.22/0.54  % (7844)------------------------------
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    spl3_29 | ~spl3_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f119,f113,f251])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl3_12 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3))) ) | ~spl3_12),
% 0.22/0.54    inference(resolution,[],[f114,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f113])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    spl3_21 | ~spl3_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f98,f94,f177])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl3_8 <=> ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X1] : (k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X1)),X1) = X1) ) | ~spl3_8),
% 0.22/0.54    inference(resolution,[],[f95,f30])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) ) | ~spl3_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f94])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    spl3_20 | ~spl3_8 | ~spl3_17),
% 0.22/0.54    inference(avatar_split_clause,[],[f169,f154,f94,f172])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    spl3_17 <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | (~spl3_8 | ~spl3_17)),
% 0.22/0.54    inference(subsumption_resolution,[],[f167,f95])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) | sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_17),
% 0.22/0.54    inference(resolution,[],[f156,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~spl3_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f154])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    spl3_17 | ~spl3_5 | ~spl3_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f152,f133,f60,f154])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    spl3_5 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    spl3_15 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | (~spl3_5 | ~spl3_15)),
% 0.22/0.54    inference(resolution,[],[f134,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl3_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f60])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) ) | ~spl3_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f133])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl3_15 | ~spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f87,f40,f133])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) ) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f29,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f40])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    spl3_12 | ~spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f81,f40,f113])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f35,f42])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl3_8 | ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f92,f50,f45,f40,f94])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    spl3_2 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    spl3_3 <=> v2_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f91,f42])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) | ~v1_relat_1(sK2)) ) | (~spl3_2 | ~spl3_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f90,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    v1_funct_1(sK2) | ~spl3_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f45])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_3),
% 0.22/0.54    inference(resolution,[],[f31,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    v2_funct_1(sK2) | ~spl3_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f50])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    spl3_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f25,f65])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f7])).
% 0.22/0.54  fof(f7,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f26,f60])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f28,f55])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f27,f50])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    v2_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f24,f45])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f23,f40])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (7840)------------------------------
% 0.22/0.54  % (7840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7840)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (7840)Memory used [KB]: 6396
% 0.22/0.54  % (7840)Time elapsed: 0.113 s
% 0.22/0.54  % (7840)------------------------------
% 0.22/0.54  % (7840)------------------------------
% 0.22/0.54  % (7834)Success in time 0.179 s
%------------------------------------------------------------------------------
