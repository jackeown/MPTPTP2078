%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:05 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 144 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  229 ( 381 expanded)
%              Number of equality atoms :   42 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1427,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f58,f62,f69,f79,f87,f138,f1235,f1297,f1324,f1370,f1426])).

fof(f1426,plain,
    ( spl3_1
    | ~ spl3_7
    | ~ spl3_187 ),
    inference(avatar_contradiction_clause,[],[f1425])).

fof(f1425,plain,
    ( $false
    | spl3_1
    | ~ spl3_7
    | ~ spl3_187 ),
    inference(subsumption_resolution,[],[f1403,f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1403,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_187 ),
    inference(trivial_inequality_removal,[],[f1402])).

fof(f1402,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_187 ),
    inference(superposition,[],[f53,f1369])).

fof(f1369,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_187 ),
    inference(avatar_component_clause,[],[f1367])).

fof(f1367,plain,
    ( spl3_187
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_187])])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1370,plain,
    ( spl3_187
    | ~ spl3_171
    | ~ spl3_173
    | ~ spl3_179 ),
    inference(avatar_split_clause,[],[f1365,f1322,f1294,f1233,f1367])).

fof(f1233,plain,
    ( spl3_171
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_171])])).

fof(f1294,plain,
    ( spl3_173
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_173])])).

fof(f1322,plain,
    ( spl3_179
  <=> ! [X13,X12] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).

fof(f1365,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_171
    | ~ spl3_173
    | ~ spl3_179 ),
    inference(subsumption_resolution,[],[f1363,f1323])).

fof(f1323,plain,
    ( ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12)
    | ~ spl3_179 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f1363,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_171
    | ~ spl3_173 ),
    inference(resolution,[],[f1296,f1234])).

fof(f1234,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_171 ),
    inference(avatar_component_clause,[],[f1233])).

fof(f1296,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_173 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1324,plain,
    ( spl3_179
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f1279,f136,f85,f1322])).

fof(f85,plain,
    ( spl3_13
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f136,plain,
    ( spl3_20
  <=> ! [X7,X8,X6] :
        ( k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8))
        | r1_tarski(k4_xboole_0(X6,X7),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1279,plain,
    ( ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12)
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f1247])).

fof(f1247,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k4_xboole_0(X12,X13),X12) )
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(superposition,[],[f137,f86])).

fof(f86,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f137,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8))
        | r1_tarski(k4_xboole_0(X6,X7),X8) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1297,plain,
    ( spl3_173
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f1287,f136,f76,f1294])).

fof(f76,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f1287,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f1239])).

fof(f1239,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(superposition,[],[f137,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f1235,plain,
    ( spl3_171
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f1231,f60,f30,f1233])).

fof(f30,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1231,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f61,f32])).

fof(f32,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f138,plain,
    ( spl3_20
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f106,f56,f52,f136])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f106,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8))
        | r1_tarski(k4_xboole_0(X6,X7),X8) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f53,f57])).

fof(f57,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f87,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f74,f66,f48,f85])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f66,plain,
    ( spl3_10
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f74,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f79,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f72,f48,f35,f76])).

fof(f35,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f69,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f64,f44,f40,f66])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f64,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f41,f45])).

fof(f45,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f41,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f62,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.36  ipcrm: permission denied for id (812613632)
% 0.21/0.37  ipcrm: permission denied for id (812777476)
% 0.21/0.37  ipcrm: permission denied for id (812843014)
% 0.21/0.38  ipcrm: permission denied for id (813039628)
% 0.21/0.38  ipcrm: permission denied for id (813072397)
% 0.21/0.38  ipcrm: permission denied for id (813170704)
% 0.21/0.38  ipcrm: permission denied for id (813203473)
% 0.21/0.39  ipcrm: permission denied for id (813236242)
% 0.21/0.39  ipcrm: permission denied for id (813367318)
% 0.21/0.39  ipcrm: permission denied for id (813465625)
% 0.21/0.40  ipcrm: permission denied for id (813563931)
% 0.21/0.40  ipcrm: permission denied for id (813596700)
% 0.21/0.40  ipcrm: permission denied for id (813629469)
% 0.21/0.40  ipcrm: permission denied for id (813662238)
% 0.21/0.40  ipcrm: permission denied for id (813760545)
% 0.21/0.41  ipcrm: permission denied for id (813826083)
% 0.21/0.41  ipcrm: permission denied for id (813924390)
% 0.21/0.41  ipcrm: permission denied for id (813989928)
% 0.21/0.41  ipcrm: permission denied for id (814055466)
% 0.21/0.42  ipcrm: permission denied for id (814121004)
% 0.21/0.42  ipcrm: permission denied for id (814153773)
% 0.21/0.42  ipcrm: permission denied for id (814252080)
% 0.21/0.42  ipcrm: permission denied for id (814284849)
% 0.21/0.42  ipcrm: permission denied for id (814317618)
% 0.21/0.43  ipcrm: permission denied for id (814383156)
% 0.21/0.43  ipcrm: permission denied for id (814448693)
% 0.21/0.43  ipcrm: permission denied for id (814514230)
% 0.21/0.43  ipcrm: permission denied for id (814645306)
% 0.21/0.43  ipcrm: permission denied for id (814710844)
% 0.21/0.44  ipcrm: permission denied for id (814743613)
% 0.21/0.44  ipcrm: permission denied for id (814809151)
% 0.21/0.44  ipcrm: permission denied for id (814874689)
% 0.21/0.44  ipcrm: permission denied for id (814907458)
% 0.21/0.44  ipcrm: permission denied for id (814940227)
% 0.21/0.44  ipcrm: permission denied for id (814972996)
% 0.21/0.45  ipcrm: permission denied for id (815005765)
% 0.21/0.45  ipcrm: permission denied for id (815071302)
% 0.21/0.45  ipcrm: permission denied for id (815136840)
% 0.21/0.45  ipcrm: permission denied for id (815202378)
% 0.21/0.45  ipcrm: permission denied for id (815235147)
% 0.21/0.45  ipcrm: permission denied for id (815267916)
% 0.21/0.45  ipcrm: permission denied for id (815300685)
% 0.21/0.46  ipcrm: permission denied for id (815431761)
% 0.21/0.46  ipcrm: permission denied for id (815464530)
% 0.21/0.46  ipcrm: permission denied for id (815497299)
% 0.21/0.46  ipcrm: permission denied for id (815530068)
% 0.21/0.46  ipcrm: permission denied for id (815562837)
% 0.21/0.47  ipcrm: permission denied for id (815595606)
% 0.21/0.47  ipcrm: permission denied for id (815661144)
% 0.21/0.47  ipcrm: permission denied for id (815693913)
% 0.21/0.47  ipcrm: permission denied for id (815726682)
% 0.21/0.47  ipcrm: permission denied for id (815857757)
% 0.21/0.47  ipcrm: permission denied for id (815890526)
% 0.21/0.48  ipcrm: permission denied for id (815988833)
% 0.21/0.48  ipcrm: permission denied for id (816021602)
% 0.21/0.48  ipcrm: permission denied for id (816054371)
% 0.21/0.48  ipcrm: permission denied for id (816152678)
% 0.21/0.49  ipcrm: permission denied for id (816185447)
% 0.21/0.49  ipcrm: permission denied for id (816250985)
% 0.21/0.49  ipcrm: permission denied for id (816382061)
% 0.21/0.49  ipcrm: permission denied for id (816414830)
% 0.21/0.50  ipcrm: permission denied for id (816578674)
% 0.21/0.50  ipcrm: permission denied for id (816611443)
% 0.21/0.50  ipcrm: permission denied for id (816644212)
% 0.21/0.50  ipcrm: permission denied for id (816742519)
% 0.21/0.51  ipcrm: permission denied for id (816775288)
% 0.21/0.51  ipcrm: permission denied for id (816808057)
% 0.21/0.51  ipcrm: permission denied for id (816939133)
% 0.21/0.51  ipcrm: permission denied for id (816971902)
% 0.21/0.57  % (8454)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.57  % (8448)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.61/0.58  % (8457)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.61/0.58  % (8452)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.61/0.59  % (8453)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.88/0.60  % (8457)Refutation found. Thanks to Tanya!
% 0.88/0.60  % SZS status Theorem for theBenchmark
% 0.88/0.60  % SZS output start Proof for theBenchmark
% 0.88/0.60  fof(f1427,plain,(
% 0.88/0.60    $false),
% 0.88/0.60    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f58,f62,f69,f79,f87,f138,f1235,f1297,f1324,f1370,f1426])).
% 0.88/0.60  fof(f1426,plain,(
% 0.88/0.60    spl3_1 | ~spl3_7 | ~spl3_187),
% 0.88/0.60    inference(avatar_contradiction_clause,[],[f1425])).
% 0.88/0.60  fof(f1425,plain,(
% 0.88/0.60    $false | (spl3_1 | ~spl3_7 | ~spl3_187)),
% 0.88/0.60    inference(subsumption_resolution,[],[f1403,f27])).
% 0.88/0.60  fof(f27,plain,(
% 0.88/0.60    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.88/0.60    inference(avatar_component_clause,[],[f25])).
% 0.88/0.60  fof(f25,plain,(
% 0.88/0.60    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.88/0.60  fof(f1403,plain,(
% 0.88/0.60    r1_tarski(sK0,sK1) | (~spl3_7 | ~spl3_187)),
% 0.88/0.60    inference(trivial_inequality_removal,[],[f1402])).
% 0.88/0.60  fof(f1402,plain,(
% 0.88/0.60    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | (~spl3_7 | ~spl3_187)),
% 0.88/0.60    inference(superposition,[],[f53,f1369])).
% 0.88/0.60  fof(f1369,plain,(
% 0.88/0.60    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_187),
% 0.88/0.60    inference(avatar_component_clause,[],[f1367])).
% 0.88/0.60  fof(f1367,plain,(
% 0.88/0.60    spl3_187 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_187])])).
% 0.88/0.60  fof(f53,plain,(
% 0.88/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.88/0.60    inference(avatar_component_clause,[],[f52])).
% 0.88/0.60  fof(f52,plain,(
% 0.88/0.60    spl3_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.88/0.60  fof(f1370,plain,(
% 0.88/0.60    spl3_187 | ~spl3_171 | ~spl3_173 | ~spl3_179),
% 0.88/0.60    inference(avatar_split_clause,[],[f1365,f1322,f1294,f1233,f1367])).
% 0.88/0.60  fof(f1233,plain,(
% 0.88/0.60    spl3_171 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK2) | ~r1_tarski(X0,sK0))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_171])])).
% 0.88/0.60  fof(f1294,plain,(
% 0.88/0.60    spl3_173 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_173])])).
% 0.88/0.60  fof(f1322,plain,(
% 0.88/0.60    spl3_179 <=> ! [X13,X12] : r1_tarski(k4_xboole_0(X12,X13),X12)),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).
% 0.88/0.60  fof(f1365,plain,(
% 0.88/0.60    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_171 | ~spl3_173 | ~spl3_179)),
% 0.88/0.60    inference(subsumption_resolution,[],[f1363,f1323])).
% 0.88/0.60  fof(f1323,plain,(
% 0.88/0.60    ( ! [X12,X13] : (r1_tarski(k4_xboole_0(X12,X13),X12)) ) | ~spl3_179),
% 0.88/0.60    inference(avatar_component_clause,[],[f1322])).
% 0.88/0.60  fof(f1363,plain,(
% 0.88/0.60    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (~spl3_171 | ~spl3_173)),
% 0.88/0.60    inference(resolution,[],[f1296,f1234])).
% 0.88/0.60  fof(f1234,plain,(
% 0.88/0.60    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK0)) ) | ~spl3_171),
% 0.88/0.60    inference(avatar_component_clause,[],[f1233])).
% 0.88/0.60  fof(f1296,plain,(
% 0.88/0.60    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl3_173),
% 0.88/0.60    inference(avatar_component_clause,[],[f1294])).
% 0.88/0.60  fof(f1324,plain,(
% 0.88/0.60    spl3_179 | ~spl3_13 | ~spl3_20),
% 0.88/0.60    inference(avatar_split_clause,[],[f1279,f136,f85,f1322])).
% 0.88/0.60  fof(f85,plain,(
% 0.88/0.60    spl3_13 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.88/0.60  fof(f136,plain,(
% 0.88/0.60    spl3_20 <=> ! [X7,X8,X6] : (k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8)) | r1_tarski(k4_xboole_0(X6,X7),X8))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.88/0.60  fof(f1279,plain,(
% 0.88/0.60    ( ! [X12,X13] : (r1_tarski(k4_xboole_0(X12,X13),X12)) ) | (~spl3_13 | ~spl3_20)),
% 0.88/0.60    inference(trivial_inequality_removal,[],[f1247])).
% 0.88/0.60  fof(f1247,plain,(
% 0.88/0.60    ( ! [X12,X13] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(X12,X13),X12)) ) | (~spl3_13 | ~spl3_20)),
% 0.88/0.60    inference(superposition,[],[f137,f86])).
% 0.88/0.60  fof(f86,plain,(
% 0.88/0.60    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | ~spl3_13),
% 0.88/0.60    inference(avatar_component_clause,[],[f85])).
% 0.88/0.60  fof(f137,plain,(
% 0.88/0.60    ( ! [X6,X8,X7] : (k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8)) | r1_tarski(k4_xboole_0(X6,X7),X8)) ) | ~spl3_20),
% 0.88/0.60    inference(avatar_component_clause,[],[f136])).
% 0.88/0.60  fof(f1297,plain,(
% 0.88/0.60    spl3_173 | ~spl3_11 | ~spl3_20),
% 0.88/0.60    inference(avatar_split_clause,[],[f1287,f136,f76,f1294])).
% 0.88/0.60  fof(f76,plain,(
% 0.88/0.60    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.88/0.60  fof(f1287,plain,(
% 0.88/0.60    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | (~spl3_11 | ~spl3_20)),
% 0.88/0.60    inference(trivial_inequality_removal,[],[f1239])).
% 0.88/0.60  fof(f1239,plain,(
% 0.88/0.60    k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,sK1),sK2) | (~spl3_11 | ~spl3_20)),
% 0.88/0.60    inference(superposition,[],[f137,f78])).
% 0.88/0.60  fof(f78,plain,(
% 0.88/0.60    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_11),
% 0.88/0.60    inference(avatar_component_clause,[],[f76])).
% 0.88/0.60  fof(f1235,plain,(
% 0.88/0.60    spl3_171 | ~spl3_2 | ~spl3_9),
% 0.88/0.60    inference(avatar_split_clause,[],[f1231,f60,f30,f1233])).
% 0.88/0.60  fof(f30,plain,(
% 0.88/0.60    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.88/0.60  fof(f60,plain,(
% 0.88/0.60    spl3_9 <=> ! [X1,X0,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.88/0.60  fof(f1231,plain,(
% 0.88/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK2) | ~r1_tarski(X0,sK0)) ) | (~spl3_2 | ~spl3_9)),
% 0.88/0.60    inference(resolution,[],[f61,f32])).
% 0.88/0.60  fof(f32,plain,(
% 0.88/0.60    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.88/0.60    inference(avatar_component_clause,[],[f30])).
% 0.88/0.60  fof(f61,plain,(
% 0.88/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.88/0.60    inference(avatar_component_clause,[],[f60])).
% 0.88/0.60  fof(f138,plain,(
% 0.88/0.60    spl3_20 | ~spl3_7 | ~spl3_8),
% 0.88/0.60    inference(avatar_split_clause,[],[f106,f56,f52,f136])).
% 0.88/0.60  fof(f56,plain,(
% 0.88/0.60    spl3_8 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.88/0.60  fof(f106,plain,(
% 0.88/0.60    ( ! [X6,X8,X7] : (k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8)) | r1_tarski(k4_xboole_0(X6,X7),X8)) ) | (~spl3_7 | ~spl3_8)),
% 0.88/0.60    inference(superposition,[],[f53,f57])).
% 0.88/0.60  fof(f57,plain,(
% 0.88/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_8),
% 0.88/0.60    inference(avatar_component_clause,[],[f56])).
% 0.88/0.60  fof(f87,plain,(
% 0.88/0.60    spl3_13 | ~spl3_6 | ~spl3_10),
% 0.88/0.60    inference(avatar_split_clause,[],[f74,f66,f48,f85])).
% 0.88/0.60  fof(f48,plain,(
% 0.88/0.60    spl3_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.88/0.60  fof(f66,plain,(
% 0.88/0.60    spl3_10 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.88/0.60  fof(f74,plain,(
% 0.88/0.60    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | (~spl3_6 | ~spl3_10)),
% 0.88/0.60    inference(resolution,[],[f49,f67])).
% 0.88/0.60  fof(f67,plain,(
% 0.88/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | ~spl3_10),
% 0.88/0.60    inference(avatar_component_clause,[],[f66])).
% 0.88/0.60  fof(f49,plain,(
% 0.88/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_6),
% 0.88/0.60    inference(avatar_component_clause,[],[f48])).
% 0.88/0.60  fof(f79,plain,(
% 0.88/0.60    spl3_11 | ~spl3_3 | ~spl3_6),
% 0.88/0.60    inference(avatar_split_clause,[],[f72,f48,f35,f76])).
% 0.88/0.60  fof(f35,plain,(
% 0.88/0.60    spl3_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.88/0.60  fof(f72,plain,(
% 0.88/0.60    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_6)),
% 0.88/0.60    inference(resolution,[],[f49,f37])).
% 0.88/0.60  fof(f37,plain,(
% 0.88/0.60    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.88/0.60    inference(avatar_component_clause,[],[f35])).
% 0.88/0.60  fof(f69,plain,(
% 0.88/0.60    spl3_10 | ~spl3_4 | ~spl3_5),
% 0.88/0.60    inference(avatar_split_clause,[],[f64,f44,f40,f66])).
% 0.88/0.60  fof(f40,plain,(
% 0.88/0.60    spl3_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.88/0.60  fof(f44,plain,(
% 0.88/0.60    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.88/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.88/0.60  fof(f64,plain,(
% 0.88/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | (~spl3_4 | ~spl3_5)),
% 0.88/0.60    inference(superposition,[],[f41,f45])).
% 0.88/0.60  fof(f45,plain,(
% 0.88/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.88/0.60    inference(avatar_component_clause,[],[f44])).
% 0.88/0.60  fof(f41,plain,(
% 0.88/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_4),
% 0.88/0.60    inference(avatar_component_clause,[],[f40])).
% 0.88/0.60  fof(f62,plain,(
% 0.88/0.60    spl3_9),
% 0.88/0.60    inference(avatar_split_clause,[],[f23,f60])).
% 0.88/0.60  fof(f23,plain,(
% 0.88/0.60    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.88/0.60    inference(cnf_transformation,[],[f11])).
% 0.88/0.60  fof(f11,plain,(
% 0.88/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.88/0.60    inference(flattening,[],[f10])).
% 0.88/0.60  fof(f10,plain,(
% 0.88/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.88/0.60    inference(ennf_transformation,[],[f4])).
% 0.88/0.60  fof(f4,axiom,(
% 0.88/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.88/0.60  fof(f58,plain,(
% 0.88/0.60    spl3_8),
% 0.88/0.60    inference(avatar_split_clause,[],[f22,f56])).
% 0.88/0.60  fof(f22,plain,(
% 0.88/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.88/0.60    inference(cnf_transformation,[],[f3])).
% 0.88/0.60  fof(f3,axiom,(
% 0.88/0.60    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.88/0.60  fof(f54,plain,(
% 0.88/0.60    spl3_7),
% 0.88/0.60    inference(avatar_split_clause,[],[f20,f52])).
% 0.88/0.60  fof(f20,plain,(
% 0.88/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.88/0.60    inference(cnf_transformation,[],[f14])).
% 0.88/0.60  fof(f14,plain,(
% 0.88/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.88/0.60    inference(nnf_transformation,[],[f2])).
% 0.88/0.60  fof(f2,axiom,(
% 0.88/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.88/0.60  fof(f50,plain,(
% 0.88/0.60    spl3_6),
% 0.88/0.60    inference(avatar_split_clause,[],[f21,f48])).
% 0.88/0.60  fof(f21,plain,(
% 0.88/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.88/0.60    inference(cnf_transformation,[],[f14])).
% 0.88/0.60  fof(f46,plain,(
% 0.88/0.60    spl3_5),
% 0.88/0.60    inference(avatar_split_clause,[],[f19,f44])).
% 0.88/0.60  fof(f19,plain,(
% 0.88/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.88/0.60    inference(cnf_transformation,[],[f1])).
% 0.88/0.60  fof(f1,axiom,(
% 0.88/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.88/0.60  fof(f42,plain,(
% 0.88/0.60    spl3_4),
% 0.88/0.60    inference(avatar_split_clause,[],[f18,f40])).
% 0.88/0.60  fof(f18,plain,(
% 0.88/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.88/0.60    inference(cnf_transformation,[],[f5])).
% 0.88/0.60  fof(f5,axiom,(
% 0.88/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.88/0.60  fof(f38,plain,(
% 0.88/0.60    spl3_3),
% 0.88/0.60    inference(avatar_split_clause,[],[f15,f35])).
% 0.88/0.60  fof(f15,plain,(
% 0.88/0.60    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.88/0.60    inference(cnf_transformation,[],[f13])).
% 0.88/0.60  fof(f13,plain,(
% 0.88/0.60    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.88/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.88/0.60  fof(f12,plain,(
% 0.88/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.88/0.60    introduced(choice_axiom,[])).
% 0.88/0.60  fof(f9,plain,(
% 0.88/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.88/0.60    inference(flattening,[],[f8])).
% 0.88/0.60  fof(f8,plain,(
% 0.88/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.88/0.60    inference(ennf_transformation,[],[f7])).
% 0.88/0.60  fof(f7,negated_conjecture,(
% 0.88/0.60    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.88/0.60    inference(negated_conjecture,[],[f6])).
% 0.88/0.60  fof(f6,conjecture,(
% 0.88/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.88/0.60  fof(f33,plain,(
% 0.88/0.60    spl3_2),
% 0.88/0.60    inference(avatar_split_clause,[],[f16,f30])).
% 0.88/0.60  fof(f16,plain,(
% 0.88/0.60    r1_xboole_0(sK0,sK2)),
% 0.88/0.60    inference(cnf_transformation,[],[f13])).
% 0.88/0.60  fof(f28,plain,(
% 0.88/0.60    ~spl3_1),
% 0.88/0.60    inference(avatar_split_clause,[],[f17,f25])).
% 0.88/0.60  fof(f17,plain,(
% 0.88/0.60    ~r1_tarski(sK0,sK1)),
% 0.88/0.60    inference(cnf_transformation,[],[f13])).
% 0.88/0.60  % SZS output end Proof for theBenchmark
% 0.88/0.60  % (8457)------------------------------
% 0.88/0.60  % (8457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.88/0.60  % (8457)Termination reason: Refutation
% 0.88/0.60  
% 0.88/0.60  % (8457)Memory used [KB]: 7291
% 0.88/0.60  % (8457)Time elapsed: 0.044 s
% 0.88/0.60  % (8457)------------------------------
% 0.88/0.60  % (8457)------------------------------
% 0.88/0.60  % (8449)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.88/0.60  % (8313)Success in time 0.248 s
%------------------------------------------------------------------------------
