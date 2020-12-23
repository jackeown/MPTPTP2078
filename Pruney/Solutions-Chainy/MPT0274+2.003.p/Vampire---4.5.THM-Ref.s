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
% DateTime   : Thu Dec  3 12:41:20 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 164 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  244 ( 439 expanded)
%              Number of equality atoms :   56 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f136,f1375,f1386,f1390,f1449,f1500,f1505,f1507,f1523])).

fof(f1523,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1521])).

fof(f1521,plain,
    ( $false
    | ~ spl3_1
    | spl3_5 ),
    inference(subsumption_resolution,[],[f135,f1450])).

fof(f1450,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f82,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f82,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f135,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_5
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1507,plain,
    ( ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f1506])).

fof(f1506,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f1499,f85,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f85,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1499,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f1497,plain,
    ( spl3_9
  <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1505,plain,
    ( ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f1501])).

fof(f1501,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f90,f1499,f46])).

fof(f90,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1500,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1460,f133,f1497])).

fof(f1460,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f103,f134])).

fof(f134,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f103,plain,(
    ! [X2,X1] : r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(superposition,[],[f75,f68])).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1449,plain,
    ( spl3_2
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f1446])).

fof(f1446,plain,
    ( $false
    | spl3_2
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f86,f169,f1385,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1385,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f1383])).

fof(f1383,plain,
    ( spl3_8
  <=> r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f169,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(superposition,[],[f166,f55])).

fof(f166,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f51,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f86,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1390,plain,
    ( spl3_3
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f1387])).

fof(f1387,plain,
    ( $false
    | spl3_3
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f91,f166,f1381,f50])).

fof(f1381,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f1379,plain,
    ( spl3_7
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f91,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f1386,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f1377,f1372,f1383,f1379])).

fof(f1372,plain,
    ( spl3_6
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1377,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_6 ),
    inference(trivial_inequality_removal,[],[f1376])).

fof(f1376,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_6 ),
    inference(superposition,[],[f1374,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f1374,plain,
    ( k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1375,plain,
    ( ~ spl3_6
    | spl3_5 ),
    inference(avatar_split_clause,[],[f1370,f133,f1372])).

fof(f1370,plain,
    ( k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_5 ),
    inference(forward_demodulation,[],[f1338,f62])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1338,plain,
    ( k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_5 ),
    inference(superposition,[],[f135,f415])).

fof(f415,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f387,f68])).

fof(f387,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f60,f69])).

fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f136,plain,
    ( spl3_3
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f116,f133,f84,f89])).

fof(f116,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f71,f68])).

fof(f71,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f45,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f92,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f89,f80])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f72,f84,f80])).

fof(f72,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f44,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:49:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (4097)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (4096)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (4094)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (4093)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (4105)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (4105)Refutation not found, incomplete strategy% (4105)------------------------------
% 0.22/0.52  % (4105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4113)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (4105)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4105)Memory used [KB]: 1663
% 0.22/0.52  % (4105)Time elapsed: 0.109 s
% 0.22/0.52  % (4105)------------------------------
% 0.22/0.52  % (4105)------------------------------
% 0.22/0.52  % (4099)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (4100)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (4095)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (4117)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (4092)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (4119)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (4111)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (4120)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (4120)Refutation not found, incomplete strategy% (4120)------------------------------
% 0.22/0.54  % (4120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4120)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4120)Memory used [KB]: 1663
% 0.22/0.54  % (4120)Time elapsed: 0.002 s
% 0.22/0.54  % (4120)------------------------------
% 0.22/0.54  % (4120)------------------------------
% 0.22/0.54  % (4118)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (4112)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (4092)Refutation not found, incomplete strategy% (4092)------------------------------
% 0.22/0.54  % (4092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4092)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4092)Memory used [KB]: 1663
% 0.22/0.54  % (4092)Time elapsed: 0.128 s
% 0.22/0.54  % (4092)------------------------------
% 0.22/0.54  % (4092)------------------------------
% 0.22/0.54  % (4091)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (4116)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (4104)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (4103)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (4110)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (4109)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (4115)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (4108)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (4119)Refutation not found, incomplete strategy% (4119)------------------------------
% 0.22/0.55  % (4119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4119)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4119)Memory used [KB]: 10746
% 0.22/0.55  % (4119)Time elapsed: 0.150 s
% 0.22/0.55  % (4119)------------------------------
% 0.22/0.55  % (4119)------------------------------
% 0.22/0.55  % (4102)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (4102)Refutation not found, incomplete strategy% (4102)------------------------------
% 0.22/0.56  % (4102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4102)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4102)Memory used [KB]: 6140
% 0.22/0.56  % (4102)Time elapsed: 0.149 s
% 0.22/0.56  % (4102)------------------------------
% 0.22/0.56  % (4102)------------------------------
% 0.22/0.56  % (4108)Refutation not found, incomplete strategy% (4108)------------------------------
% 0.22/0.56  % (4108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4101)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (4108)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4108)Memory used [KB]: 1663
% 0.22/0.56  % (4108)Time elapsed: 0.151 s
% 0.22/0.56  % (4108)------------------------------
% 0.22/0.56  % (4108)------------------------------
% 0.22/0.56  % (4107)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (4101)Refutation not found, incomplete strategy% (4101)------------------------------
% 0.22/0.56  % (4101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4101)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4101)Memory used [KB]: 10746
% 0.22/0.56  % (4101)Time elapsed: 0.159 s
% 0.22/0.56  % (4101)------------------------------
% 0.22/0.56  % (4101)------------------------------
% 0.22/0.56  % (4107)Refutation not found, incomplete strategy% (4107)------------------------------
% 0.22/0.56  % (4107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4107)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4107)Memory used [KB]: 10618
% 0.22/0.56  % (4107)Time elapsed: 0.159 s
% 0.22/0.56  % (4107)------------------------------
% 0.22/0.56  % (4107)------------------------------
% 0.22/0.56  % (4117)Refutation not found, incomplete strategy% (4117)------------------------------
% 0.22/0.56  % (4117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4117)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4117)Memory used [KB]: 6268
% 0.22/0.56  % (4117)Time elapsed: 0.159 s
% 0.22/0.56  % (4117)------------------------------
% 0.22/0.56  % (4117)------------------------------
% 1.48/0.57  % (4114)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.72/0.59  % (4098)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.72/0.59  % (4106)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.14/0.66  % (4127)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.14/0.68  % (4124)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.14/0.68  % (4135)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.14/0.70  % (4114)Refutation found. Thanks to Tanya!
% 2.14/0.70  % SZS status Theorem for theBenchmark
% 2.14/0.70  % SZS output start Proof for theBenchmark
% 2.14/0.70  fof(f1524,plain,(
% 2.14/0.70    $false),
% 2.14/0.70    inference(avatar_sat_refutation,[],[f87,f92,f136,f1375,f1386,f1390,f1449,f1500,f1505,f1507,f1523])).
% 2.14/0.70  fof(f1523,plain,(
% 2.14/0.70    ~spl3_1 | spl3_5),
% 2.14/0.70    inference(avatar_contradiction_clause,[],[f1521])).
% 2.14/0.70  fof(f1521,plain,(
% 2.14/0.70    $false | (~spl3_1 | spl3_5)),
% 2.14/0.70    inference(subsumption_resolution,[],[f135,f1450])).
% 2.14/0.70  fof(f1450,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_1),
% 2.14/0.70    inference(forward_demodulation,[],[f82,f68])).
% 2.14/0.70  fof(f68,plain,(
% 2.14/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f1])).
% 2.14/0.70  fof(f1,axiom,(
% 2.14/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.14/0.70  fof(f82,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~spl3_1),
% 2.14/0.70    inference(avatar_component_clause,[],[f80])).
% 2.14/0.70  fof(f80,plain,(
% 2.14/0.70    spl3_1 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.14/0.70  fof(f135,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_5),
% 2.14/0.70    inference(avatar_component_clause,[],[f133])).
% 2.14/0.70  fof(f133,plain,(
% 2.14/0.70    spl3_5 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.14/0.70  fof(f1507,plain,(
% 2.14/0.70    ~spl3_2 | ~spl3_9),
% 2.14/0.70    inference(avatar_contradiction_clause,[],[f1506])).
% 2.14/0.70  fof(f1506,plain,(
% 2.14/0.70    $false | (~spl3_2 | ~spl3_9)),
% 2.14/0.70    inference(unit_resulting_resolution,[],[f1499,f85,f161])).
% 2.14/0.70  fof(f161,plain,(
% 2.14/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X1,X0),X2) | ~r2_hidden(X0,X2)) )),
% 2.14/0.70    inference(superposition,[],[f46,f55])).
% 2.14/0.70  fof(f55,plain,(
% 2.14/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f14])).
% 2.14/0.70  fof(f14,axiom,(
% 2.14/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.14/0.70  fof(f46,plain,(
% 2.14/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f29])).
% 2.14/0.70  fof(f29,plain,(
% 2.14/0.70    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.14/0.70    inference(ennf_transformation,[],[f24])).
% 2.14/0.70  fof(f24,axiom,(
% 2.14/0.70    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 2.14/0.70  fof(f85,plain,(
% 2.14/0.70    r2_hidden(sK1,sK2) | ~spl3_2),
% 2.14/0.70    inference(avatar_component_clause,[],[f84])).
% 2.14/0.70  fof(f84,plain,(
% 2.14/0.70    spl3_2 <=> r2_hidden(sK1,sK2)),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.14/0.70  fof(f1499,plain,(
% 2.14/0.70    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_9),
% 2.14/0.70    inference(avatar_component_clause,[],[f1497])).
% 2.14/0.70  fof(f1497,plain,(
% 2.14/0.70    spl3_9 <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.14/0.70  fof(f1505,plain,(
% 2.14/0.70    ~spl3_3 | ~spl3_9),
% 2.14/0.70    inference(avatar_contradiction_clause,[],[f1501])).
% 2.14/0.70  fof(f1501,plain,(
% 2.14/0.70    $false | (~spl3_3 | ~spl3_9)),
% 2.14/0.70    inference(unit_resulting_resolution,[],[f90,f1499,f46])).
% 2.14/0.70  fof(f90,plain,(
% 2.14/0.70    r2_hidden(sK0,sK2) | ~spl3_3),
% 2.14/0.70    inference(avatar_component_clause,[],[f89])).
% 2.14/0.70  fof(f89,plain,(
% 2.14/0.70    spl3_3 <=> r2_hidden(sK0,sK2)),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.14/0.70  fof(f1500,plain,(
% 2.14/0.70    spl3_9 | ~spl3_5),
% 2.14/0.70    inference(avatar_split_clause,[],[f1460,f133,f1497])).
% 2.14/0.70  fof(f1460,plain,(
% 2.14/0.70    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_5),
% 2.14/0.70    inference(superposition,[],[f103,f134])).
% 2.14/0.70  fof(f134,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_5),
% 2.14/0.70    inference(avatar_component_clause,[],[f133])).
% 2.14/0.70  fof(f103,plain,(
% 2.14/0.70    ( ! [X2,X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)) )),
% 2.14/0.70    inference(superposition,[],[f75,f68])).
% 2.14/0.70  fof(f75,plain,(
% 2.14/0.70    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.14/0.70    inference(definition_unfolding,[],[f58,f56])).
% 2.14/0.70  fof(f56,plain,(
% 2.14/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.14/0.70    inference(cnf_transformation,[],[f7])).
% 2.14/0.70  fof(f7,axiom,(
% 2.14/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.14/0.70  fof(f58,plain,(
% 2.14/0.70    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f12])).
% 2.14/0.70  fof(f12,axiom,(
% 2.14/0.70    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.14/0.70  fof(f1449,plain,(
% 2.14/0.70    spl3_2 | spl3_8),
% 2.14/0.70    inference(avatar_contradiction_clause,[],[f1446])).
% 2.14/0.70  fof(f1446,plain,(
% 2.14/0.70    $false | (spl3_2 | spl3_8)),
% 2.14/0.70    inference(unit_resulting_resolution,[],[f86,f169,f1385,f50])).
% 2.14/0.70  fof(f50,plain,(
% 2.14/0.70    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f38])).
% 2.14/0.70  fof(f38,plain,(
% 2.14/0.70    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.14/0.70    inference(nnf_transformation,[],[f30])).
% 2.14/0.70  fof(f30,plain,(
% 2.14/0.70    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.14/0.70    inference(ennf_transformation,[],[f5])).
% 2.14/0.70  fof(f5,axiom,(
% 2.14/0.70    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.14/0.70  fof(f1385,plain,(
% 2.14/0.70    ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_8),
% 2.14/0.70    inference(avatar_component_clause,[],[f1383])).
% 2.14/0.70  fof(f1383,plain,(
% 2.14/0.70    spl3_8 <=> r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.14/0.70  fof(f169,plain,(
% 2.14/0.70    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 2.14/0.70    inference(superposition,[],[f166,f55])).
% 2.14/0.70  fof(f166,plain,(
% 2.14/0.70    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.14/0.70    inference(resolution,[],[f51,f77])).
% 2.14/0.70  fof(f77,plain,(
% 2.14/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.14/0.70    inference(equality_resolution,[],[f65])).
% 2.14/0.70  fof(f65,plain,(
% 2.14/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.14/0.70    inference(cnf_transformation,[],[f42])).
% 2.14/0.70  fof(f42,plain,(
% 2.14/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.70    inference(flattening,[],[f41])).
% 2.14/0.70  fof(f41,plain,(
% 2.14/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.70    inference(nnf_transformation,[],[f6])).
% 2.14/0.70  fof(f6,axiom,(
% 2.14/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.70  fof(f51,plain,(
% 2.14/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f40])).
% 2.14/0.70  fof(f40,plain,(
% 2.14/0.70    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.14/0.70    inference(flattening,[],[f39])).
% 2.14/0.70  fof(f39,plain,(
% 2.14/0.70    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.14/0.70    inference(nnf_transformation,[],[f22])).
% 2.14/0.70  fof(f22,axiom,(
% 2.14/0.70    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.14/0.70  fof(f86,plain,(
% 2.14/0.70    ~r2_hidden(sK1,sK2) | spl3_2),
% 2.14/0.70    inference(avatar_component_clause,[],[f84])).
% 2.14/0.70  fof(f1390,plain,(
% 2.14/0.70    spl3_3 | spl3_7),
% 2.14/0.70    inference(avatar_contradiction_clause,[],[f1387])).
% 2.14/0.70  fof(f1387,plain,(
% 2.14/0.70    $false | (spl3_3 | spl3_7)),
% 2.14/0.70    inference(unit_resulting_resolution,[],[f91,f166,f1381,f50])).
% 2.14/0.70  fof(f1381,plain,(
% 2.14/0.70    ~r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_7),
% 2.14/0.70    inference(avatar_component_clause,[],[f1379])).
% 2.14/0.70  fof(f1379,plain,(
% 2.14/0.70    spl3_7 <=> r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.14/0.70  fof(f91,plain,(
% 2.14/0.70    ~r2_hidden(sK0,sK2) | spl3_3),
% 2.14/0.70    inference(avatar_component_clause,[],[f89])).
% 2.14/0.70  fof(f1386,plain,(
% 2.14/0.70    ~spl3_7 | ~spl3_8 | spl3_6),
% 2.14/0.70    inference(avatar_split_clause,[],[f1377,f1372,f1383,f1379])).
% 2.14/0.70  fof(f1372,plain,(
% 2.14/0.70    spl3_6 <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.14/0.70  fof(f1377,plain,(
% 2.14/0.70    ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_6),
% 2.14/0.70    inference(trivial_inequality_removal,[],[f1376])).
% 2.14/0.70  fof(f1376,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_6),
% 2.14/0.70    inference(superposition,[],[f1374,f54])).
% 2.14/0.70  fof(f54,plain,(
% 2.14/0.70    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f32])).
% 2.14/0.70  fof(f32,plain,(
% 2.14/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 2.14/0.70    inference(flattening,[],[f31])).
% 2.14/0.70  fof(f31,plain,(
% 2.14/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 2.14/0.70    inference(ennf_transformation,[],[f23])).
% 2.14/0.70  fof(f23,axiom,(
% 2.14/0.70    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 2.14/0.70  fof(f1374,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_6),
% 2.14/0.70    inference(avatar_component_clause,[],[f1372])).
% 2.14/0.70  fof(f1375,plain,(
% 2.14/0.70    ~spl3_6 | spl3_5),
% 2.14/0.70    inference(avatar_split_clause,[],[f1370,f133,f1372])).
% 2.14/0.70  fof(f1370,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_5),
% 2.14/0.70    inference(forward_demodulation,[],[f1338,f62])).
% 2.14/0.70  fof(f62,plain,(
% 2.14/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f2])).
% 2.14/0.70  fof(f2,axiom,(
% 2.14/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.14/0.70  fof(f1338,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) != k3_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_5),
% 2.14/0.70    inference(superposition,[],[f135,f415])).
% 2.14/0.70  fof(f415,plain,(
% 2.14/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.14/0.70    inference(forward_demodulation,[],[f387,f68])).
% 2.14/0.70  fof(f387,plain,(
% 2.14/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 2.14/0.70    inference(superposition,[],[f60,f69])).
% 2.14/0.70  fof(f69,plain,(
% 2.14/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.14/0.70    inference(cnf_transformation,[],[f27])).
% 2.14/0.70  fof(f27,plain,(
% 2.14/0.70    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.14/0.70    inference(rectify,[],[f3])).
% 2.14/0.70  fof(f3,axiom,(
% 2.14/0.70    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.14/0.70  fof(f60,plain,(
% 2.14/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.14/0.70    inference(cnf_transformation,[],[f8])).
% 2.14/0.70  fof(f8,axiom,(
% 2.14/0.70    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.14/0.70  fof(f136,plain,(
% 2.14/0.70    spl3_3 | spl3_2 | ~spl3_5),
% 2.14/0.70    inference(avatar_split_clause,[],[f116,f133,f84,f89])).
% 2.14/0.70  fof(f116,plain,(
% 2.14/0.70    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 2.14/0.70    inference(forward_demodulation,[],[f71,f68])).
% 2.14/0.70  fof(f71,plain,(
% 2.14/0.70    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.14/0.70    inference(definition_unfolding,[],[f45,f56])).
% 2.14/0.70  fof(f45,plain,(
% 2.14/0.70    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.14/0.70    inference(cnf_transformation,[],[f37])).
% 2.14/0.70  fof(f37,plain,(
% 2.14/0.70    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.14/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f36])).
% 2.14/0.70  fof(f36,plain,(
% 2.14/0.70    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 2.14/0.70    introduced(choice_axiom,[])).
% 2.14/0.70  fof(f35,plain,(
% 2.14/0.70    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.14/0.70    inference(flattening,[],[f34])).
% 2.14/0.70  fof(f34,plain,(
% 2.14/0.70    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.14/0.70    inference(nnf_transformation,[],[f28])).
% 2.14/0.70  fof(f28,plain,(
% 2.14/0.70    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.14/0.70    inference(ennf_transformation,[],[f26])).
% 2.14/0.70  fof(f26,negated_conjecture,(
% 2.14/0.70    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.14/0.70    inference(negated_conjecture,[],[f25])).
% 2.14/0.70  fof(f25,conjecture,(
% 2.14/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.14/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.14/0.70  fof(f92,plain,(
% 2.14/0.70    spl3_1 | ~spl3_3),
% 2.14/0.70    inference(avatar_split_clause,[],[f73,f89,f80])).
% 2.14/0.70  fof(f73,plain,(
% 2.14/0.70    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.14/0.70    inference(definition_unfolding,[],[f43,f56])).
% 2.14/0.70  fof(f43,plain,(
% 2.14/0.70    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.14/0.70    inference(cnf_transformation,[],[f37])).
% 2.14/0.70  fof(f87,plain,(
% 2.14/0.70    spl3_1 | ~spl3_2),
% 2.14/0.70    inference(avatar_split_clause,[],[f72,f84,f80])).
% 2.14/0.70  fof(f72,plain,(
% 2.14/0.70    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.14/0.70    inference(definition_unfolding,[],[f44,f56])).
% 2.14/0.70  fof(f44,plain,(
% 2.14/0.70    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.14/0.70    inference(cnf_transformation,[],[f37])).
% 2.14/0.70  % SZS output end Proof for theBenchmark
% 2.14/0.70  % (4114)------------------------------
% 2.14/0.70  % (4114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.70  % (4114)Termination reason: Refutation
% 2.14/0.70  
% 2.14/0.70  % (4114)Memory used [KB]: 12025
% 2.14/0.70  % (4114)Time elapsed: 0.209 s
% 2.14/0.70  % (4114)------------------------------
% 2.14/0.70  % (4114)------------------------------
% 2.45/0.71  % (4128)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.45/0.72  % (4128)Refutation not found, incomplete strategy% (4128)------------------------------
% 2.45/0.72  % (4128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.45/0.72  % (4128)Termination reason: Refutation not found, incomplete strategy
% 2.45/0.72  
% 2.45/0.72  % (4128)Memory used [KB]: 6140
% 2.45/0.72  % (4128)Time elapsed: 0.139 s
% 2.45/0.72  % (4128)------------------------------
% 2.45/0.72  % (4128)------------------------------
% 2.45/0.72  % (4090)Success in time 0.354 s
%------------------------------------------------------------------------------
