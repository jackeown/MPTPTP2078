%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 321 expanded)
%              Number of leaves         :   23 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  336 ( 859 expanded)
%              Number of equality atoms :   70 ( 254 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1414,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f64,f186,f302,f1130,f1160,f1164,f1190,f1267,f1289,f1412])).

fof(f1412,plain,(
    spl3_56 ),
    inference(avatar_contradiction_clause,[],[f1405])).

fof(f1405,plain,
    ( $false
    | spl3_56 ),
    inference(resolution,[],[f1270,f67])).

fof(f67,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( X0 != X0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1270,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_56 ),
    inference(resolution,[],[f1263,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f68,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X1,X2),X0)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f43,f41])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1263,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))
    | spl3_56 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1261,plain,
    ( spl3_56
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f1289,plain,
    ( spl3_2
    | ~ spl3_57 ),
    inference(avatar_contradiction_clause,[],[f1288])).

fof(f1288,plain,
    ( $false
    | spl3_2
    | ~ spl3_57 ),
    inference(resolution,[],[f1287,f62])).

fof(f62,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1287,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_57 ),
    inference(duplicate_literal_removal,[],[f1283])).

fof(f1283,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_57 ),
    inference(resolution,[],[f1266,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1266,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),X1),sK0)
        | r1_xboole_0(k1_relat_1(sK1),X1) )
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f1265])).

fof(f1265,plain,
    ( spl3_57
  <=> ! [X1] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),X1),sK0)
        | r1_xboole_0(k1_relat_1(sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f1267,plain,
    ( ~ spl3_56
    | spl3_57
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f1258,f1188,f1265,f1261])).

fof(f1188,plain,
    ( spl3_50
  <=> ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f1258,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),X1),sK0)
        | r1_xboole_0(k1_relat_1(sK1),X1)
        | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) )
    | ~ spl3_50 ),
    inference(duplicate_literal_removal,[],[f1255])).

fof(f1255,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(k1_relat_1(sK1),X1),sK0)
        | r1_xboole_0(k1_relat_1(sK1),X1)
        | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))
        | r1_xboole_0(k1_relat_1(sK1),X1) )
    | ~ spl3_50 ),
    inference(resolution,[],[f1214,f68])).

fof(f1214,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_relat_1(sK1),X0),k1_xboole_0)
        | ~ r2_hidden(sK2(k1_relat_1(sK1),X0),sK0)
        | r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl3_50 ),
    inference(resolution,[],[f1189,f41])).

fof(f1189,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | r2_hidden(X2,k1_xboole_0) )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f1188])).

fof(f1190,plain,
    ( ~ spl3_48
    | spl3_50
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1186,f153,f56,f1188,f1123])).

fof(f1123,plain,
    ( spl3_48
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f56,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f153,plain,
    ( spl3_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1186,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f1171,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f1171,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_1 ),
    inference(superposition,[],[f50,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f1164,plain,(
    spl3_49 ),
    inference(avatar_contradiction_clause,[],[f1163])).

fof(f1163,plain,
    ( $false
    | spl3_49 ),
    inference(resolution,[],[f1161,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f1161,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_49 ),
    inference(resolution,[],[f1129,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1129,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1127,plain,
    ( spl3_49
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f1160,plain,(
    spl3_48 ),
    inference(avatar_contradiction_clause,[],[f1159])).

fof(f1159,plain,
    ( $false
    | spl3_48 ),
    inference(resolution,[],[f1125,f31])).

fof(f1125,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_48 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1130,plain,
    ( ~ spl3_2
    | ~ spl3_48
    | ~ spl3_49
    | spl3_1 ),
    inference(avatar_split_clause,[],[f1121,f56,f1127,f1123,f60])).

fof(f1121,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f1069])).

fof(f1069,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_1 ),
    inference(superposition,[],[f58,f176])).

fof(f176,plain,(
    ! [X19,X20] :
      ( k1_xboole_0 = k7_relat_1(X19,X20)
      | ~ v1_relat_1(k7_relat_1(X19,X20))
      | ~ v1_relat_1(X19)
      | ~ r1_xboole_0(k1_relat_1(X19),X20) ) ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,(
    ! [X19,X20] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k7_relat_1(X19,X20)
      | ~ v1_relat_1(k7_relat_1(X19,X20))
      | ~ v1_relat_1(X19)
      | ~ r1_xboole_0(k1_relat_1(X19),X20) ) ),
    inference(superposition,[],[f36,f93])).

fof(f93,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k1_relat_1(k7_relat_1(X3,X4))
      | ~ v1_relat_1(X3)
      | ~ r1_xboole_0(k1_relat_1(X3),X4) ) ),
    inference(forward_demodulation,[],[f86,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f72,f35])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f51,plain,(
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

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f86,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k7_relat_1(X3,X4)) = k4_xboole_0(k1_relat_1(X3),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ r1_xboole_0(k1_relat_1(X3),X4) ) ),
    inference(superposition,[],[f81,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f58,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f302,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl3_7 ),
    inference(resolution,[],[f276,f31])).

fof(f276,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl3_7 ),
    inference(resolution,[],[f260,f67])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f185,f44])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,k1_xboole_0))
        | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f186,plain,
    ( spl3_7
    | spl3_4 ),
    inference(avatar_split_clause,[],[f182,f153,f184])).

fof(f182,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f93,f99])).

fof(f99,plain,(
    ! [X6] :
      ( k1_xboole_0 = k7_relat_1(X6,k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(X6,k1_xboole_0))
      | ~ v1_relat_1(X6) ) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k7_relat_1(X6,k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(X6,k1_xboole_0))
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f36,f92])).

fof(f92,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_relat_1(k7_relat_1(X2,k1_xboole_0))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f85,f74])).

fof(f85,plain,(
    ! [X2] :
      ( k1_relat_1(k7_relat_1(X2,k1_xboole_0)) = k4_xboole_0(k1_relat_1(X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f81,f35])).

fof(f64,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f32,f60,f56])).

fof(f32,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f60,f56])).

fof(f33,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (27586)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.46  % (27580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (27578)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (27590)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (27582)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (27589)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (27588)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (27579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (27576)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (27581)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (27580)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f1414,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f63,f64,f186,f302,f1130,f1160,f1164,f1190,f1267,f1289,f1412])).
% 0.22/0.49  fof(f1412,plain,(
% 0.22/0.49    spl3_56),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f1405])).
% 0.22/0.49  fof(f1405,plain,(
% 0.22/0.49    $false | spl3_56),
% 0.22/0.49    inference(resolution,[],[f1270,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0] : (X0 != X0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(superposition,[],[f47,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.49  fof(f1270,plain,(
% 0.22/0.49    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl3_56),
% 0.22/0.49    inference(resolution,[],[f1263,f129])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f124])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f68,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X1,X2),X0) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X2)) )),
% 0.22/0.49    inference(resolution,[],[f43,f41])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f1263,plain,(
% 0.22/0.49    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) | spl3_56),
% 0.22/0.49    inference(avatar_component_clause,[],[f1261])).
% 0.22/0.49  fof(f1261,plain,(
% 0.22/0.49    spl3_56 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.49  fof(f1289,plain,(
% 0.22/0.49    spl3_2 | ~spl3_57),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f1288])).
% 0.22/0.49  fof(f1288,plain,(
% 0.22/0.49    $false | (spl3_2 | ~spl3_57)),
% 0.22/0.49    inference(resolution,[],[f1287,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl3_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f1287,plain,(
% 0.22/0.49    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_57),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f1283])).
% 0.22/0.49  fof(f1283,plain,(
% 0.22/0.49    r1_xboole_0(k1_relat_1(sK1),sK0) | r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_57),
% 0.22/0.49    inference(resolution,[],[f1266,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f1266,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(sK2(k1_relat_1(sK1),X1),sK0) | r1_xboole_0(k1_relat_1(sK1),X1)) ) | ~spl3_57),
% 0.22/0.49    inference(avatar_component_clause,[],[f1265])).
% 0.22/0.49  fof(f1265,plain,(
% 0.22/0.49    spl3_57 <=> ! [X1] : (~r2_hidden(sK2(k1_relat_1(sK1),X1),sK0) | r1_xboole_0(k1_relat_1(sK1),X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.49  fof(f1267,plain,(
% 0.22/0.49    ~spl3_56 | spl3_57 | ~spl3_50),
% 0.22/0.49    inference(avatar_split_clause,[],[f1258,f1188,f1265,f1261])).
% 0.22/0.49  fof(f1188,plain,(
% 0.22/0.49    spl3_50 <=> ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k1_relat_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.49  fof(f1258,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(sK2(k1_relat_1(sK1),X1),sK0) | r1_xboole_0(k1_relat_1(sK1),X1) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))) ) | ~spl3_50),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f1255])).
% 0.22/0.49  fof(f1255,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(sK2(k1_relat_1(sK1),X1),sK0) | r1_xboole_0(k1_relat_1(sK1),X1) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) | r1_xboole_0(k1_relat_1(sK1),X1)) ) | ~spl3_50),
% 0.22/0.49    inference(resolution,[],[f1214,f68])).
% 0.22/0.49  fof(f1214,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK1),X0),k1_xboole_0) | ~r2_hidden(sK2(k1_relat_1(sK1),X0),sK0) | r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl3_50),
% 0.22/0.49    inference(resolution,[],[f1189,f41])).
% 0.22/0.49  fof(f1189,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0) | r2_hidden(X2,k1_xboole_0)) ) | ~spl3_50),
% 0.22/0.49    inference(avatar_component_clause,[],[f1188])).
% 0.22/0.49  fof(f1190,plain,(
% 0.22/0.49    ~spl3_48 | spl3_50 | ~spl3_1 | ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f1186,f153,f56,f1188,f1123])).
% 0.22/0.49  fof(f1123,plain,(
% 0.22/0.49    spl3_48 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl3_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    spl3_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f1186,plain,(
% 0.22/0.49    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0) | ~v1_relat_1(sK1)) ) | (~spl3_1 | ~spl3_4)),
% 0.22/0.49    inference(forward_demodulation,[],[f1171,f155])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f153])).
% 0.22/0.49  fof(f1171,plain,(
% 0.22/0.49    ( ! [X2] : (r2_hidden(X2,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0) | ~v1_relat_1(sK1)) ) | ~spl3_1),
% 0.22/0.49    inference(superposition,[],[f50,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.49  fof(f1164,plain,(
% 0.22/0.49    spl3_49),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f1163])).
% 0.22/0.49  fof(f1163,plain,(
% 0.22/0.49    $false | spl3_49),
% 0.22/0.49    inference(resolution,[],[f1161,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.49  fof(f1161,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl3_49),
% 0.22/0.49    inference(resolution,[],[f1129,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.49  fof(f1129,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl3_49),
% 0.22/0.49    inference(avatar_component_clause,[],[f1127])).
% 0.22/0.49  fof(f1127,plain,(
% 0.22/0.49    spl3_49 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.49  fof(f1160,plain,(
% 0.22/0.49    spl3_48),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f1159])).
% 0.22/0.49  fof(f1159,plain,(
% 0.22/0.49    $false | spl3_48),
% 0.22/0.49    inference(resolution,[],[f1125,f31])).
% 0.22/0.49  fof(f1125,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl3_48),
% 0.22/0.49    inference(avatar_component_clause,[],[f1123])).
% 0.22/0.49  fof(f1130,plain,(
% 0.22/0.49    ~spl3_2 | ~spl3_48 | ~spl3_49 | spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f1121,f56,f1127,f1123,f60])).
% 0.22/0.49  fof(f1121,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_1),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f1069])).
% 0.22/0.49  fof(f1069,plain,(
% 0.22/0.49    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_1),
% 0.22/0.49    inference(superposition,[],[f58,f176])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    ( ! [X19,X20] : (k1_xboole_0 = k7_relat_1(X19,X20) | ~v1_relat_1(k7_relat_1(X19,X20)) | ~v1_relat_1(X19) | ~r1_xboole_0(k1_relat_1(X19),X20)) )),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f175])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ( ! [X19,X20] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(X19,X20) | ~v1_relat_1(k7_relat_1(X19,X20)) | ~v1_relat_1(X19) | ~r1_xboole_0(k1_relat_1(X19),X20)) )),
% 0.22/0.49    inference(superposition,[],[f36,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k1_xboole_0 = k1_relat_1(k7_relat_1(X3,X4)) | ~v1_relat_1(X3) | ~r1_xboole_0(k1_relat_1(X3),X4)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f86,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f72,f35])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.49    inference(superposition,[],[f53,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f34,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f38,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f40,f51])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(X3,X4)) = k4_xboole_0(k1_relat_1(X3),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~r1_xboole_0(k1_relat_1(X3),X4)) )),
% 0.22/0.49    inference(superposition,[],[f81,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f54,f53])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f45,f51])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~spl3_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f298])).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    $false | ~spl3_7),
% 0.22/0.49    inference(resolution,[],[f276,f31])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl3_7),
% 0.22/0.49    inference(resolution,[],[f260,f67])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_xboole_0(k1_relat_1(X0),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_7),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f257])).
% 0.22/0.49  fof(f257,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_7),
% 0.22/0.49    inference(resolution,[],[f185,f44])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(k7_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0)) ) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f184])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    spl3_7 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,k1_xboole_0)) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    spl3_7 | spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f182,f153,f184])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0) | ~v1_relat_1(k7_relat_1(X0,k1_xboole_0))) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f166])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0) | ~v1_relat_1(k7_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(superposition,[],[f93,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ( ! [X6] : (k1_xboole_0 = k7_relat_1(X6,k1_xboole_0) | ~v1_relat_1(k7_relat_1(X6,k1_xboole_0)) | ~v1_relat_1(X6)) )),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(X6,k1_xboole_0) | ~v1_relat_1(k7_relat_1(X6,k1_xboole_0)) | ~v1_relat_1(X6)) )),
% 0.22/0.49    inference(superposition,[],[f36,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X2] : (k1_xboole_0 = k1_relat_1(k7_relat_1(X2,k1_xboole_0)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f85,f74])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X2] : (k1_relat_1(k7_relat_1(X2,k1_xboole_0)) = k4_xboole_0(k1_relat_1(X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(superposition,[],[f81,f35])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl3_1 | spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f60,f56])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f60,f56])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27580)------------------------------
% 0.22/0.49  % (27580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27580)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27580)Memory used [KB]: 6780
% 0.22/0.49  % (27580)Time elapsed: 0.061 s
% 0.22/0.49  % (27580)------------------------------
% 0.22/0.49  % (27580)------------------------------
% 0.22/0.50  % (27575)Success in time 0.137 s
%------------------------------------------------------------------------------
