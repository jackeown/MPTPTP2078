%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:27 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  103 (1566 expanded)
%              Number of leaves         :   22 ( 441 expanded)
%              Depth                    :   25
%              Number of atoms          :  240 (6466 expanded)
%              Number of equality atoms :   62 (1516 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1682,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f1164,f1668,f1681])).

fof(f1681,plain,
    ( spl4_1
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f1676])).

fof(f1676,plain,
    ( $false
    | spl4_1
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f85,f1163,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1163,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1161,plain,
    ( spl4_10
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f85,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1668,plain,
    ( ~ spl4_2
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f1647])).

fof(f1647,plain,
    ( $false
    | ~ spl4_2
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f90,f899,f1284,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1284,plain,(
    ! [X15,X16] : r1_tarski(X16,k5_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(X16,X15)))) ),
    inference(forward_demodulation,[],[f1283,f238])).

fof(f238,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f225,f58])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f225,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f138,f127])).

fof(f127,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(global_subsumption,[],[f117,f125])).

fof(f125,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k5_xboole_0(X0,X0)),X0)
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f121,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f79,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k5_xboole_0(X0,X0)),X0)
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f114,f49])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f78,f62])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f138,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f59,f127])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1283,plain,(
    ! [X15,X16] : r1_tarski(k5_xboole_0(k1_xboole_0,X16),k5_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(k5_xboole_0(k1_xboole_0,X16),X15)))) ),
    inference(forward_demodulation,[],[f1282,f59])).

fof(f1282,plain,(
    ! [X15,X16] : r1_tarski(k5_xboole_0(k1_xboole_0,X16),k5_xboole_0(k5_xboole_0(X15,X16),k3_xboole_0(k5_xboole_0(k1_xboole_0,X16),X15))) ),
    inference(forward_demodulation,[],[f1264,f631])).

fof(f631,plain,(
    ! [X14,X13] : k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13) ),
    inference(forward_demodulation,[],[f613,f238])).

fof(f613,plain,(
    ! [X14,X13] : k5_xboole_0(X13,X14) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X14),X13) ),
    inference(superposition,[],[f572,f138])).

fof(f572,plain,(
    ! [X17,X18] : k5_xboole_0(k5_xboole_0(X18,X17),X18) = X17 ),
    inference(superposition,[],[f524,f524])).

fof(f524,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3 ),
    inference(superposition,[],[f499,f238])).

fof(f499,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f472,f58])).

fof(f472,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f138,f141])).

fof(f141,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f59,f127])).

fof(f1264,plain,(
    ! [X15,X16] : r1_tarski(k5_xboole_0(k1_xboole_0,X16),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,X16),X15),k5_xboole_0(X15,X16))) ),
    inference(superposition,[],[f941,f137])).

fof(f137,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f59,f58])).

fof(f941,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(k3_xboole_0(X23,X24),k5_xboole_0(X24,X23))) ),
    inference(forward_demodulation,[],[f919,f631])).

fof(f919,plain,(
    ! [X24,X23] : r1_tarski(X23,k5_xboole_0(k5_xboole_0(X24,X23),k3_xboole_0(X23,X24))) ),
    inference(superposition,[],[f794,f524])).

fof(f794,plain,(
    ! [X2,X3] : r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X2,k5_xboole_0(X2,X3)))) ),
    inference(forward_demodulation,[],[f793,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f793,plain,(
    ! [X2,X3] : r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X2,X3),X2))) ),
    inference(forward_demodulation,[],[f758,f238])).

fof(f758,plain,(
    ! [X2,X3] : r1_tarski(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X2,X3),X2)))) ),
    inference(superposition,[],[f148,f138])).

fof(f148,plain,(
    ! [X19,X20,X18] : r1_tarski(X20,k5_xboole_0(X20,k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(k5_xboole_0(X18,X19),X20))))) ),
    inference(superposition,[],[f76,f59])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f899,plain,
    ( sK1 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f898])).

fof(f898,plain,
    ( spl4_8
  <=> sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f90,plain,
    ( r1_tarski(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_2
  <=> r1_tarski(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1164,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f1132,f898,f1161])).

fof(f1132,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_8 ),
    inference(superposition,[],[f76,f900])).

fof(f900,plain,
    ( sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f898])).

fof(f91,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f66,f88])).

fof(f66,plain,(
    r1_tarski(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),sK1) ),
    inference(definition_unfolding,[],[f38,f63,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f86,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (23950)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (23963)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (23957)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (23939)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (23955)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (23947)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (23966)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (23943)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (23948)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (23944)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (23949)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (23960)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (23940)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (23940)Refutation not found, incomplete strategy% (23940)------------------------------
% 0.22/0.54  % (23940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23940)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23940)Memory used [KB]: 1663
% 0.22/0.54  % (23940)Time elapsed: 0.113 s
% 0.22/0.54  % (23940)------------------------------
% 0.22/0.54  % (23940)------------------------------
% 0.22/0.54  % (23961)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (23955)Refutation not found, incomplete strategy% (23955)------------------------------
% 0.22/0.54  % (23955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23955)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23955)Memory used [KB]: 10618
% 0.22/0.54  % (23955)Time elapsed: 0.126 s
% 0.22/0.54  % (23955)------------------------------
% 0.22/0.54  % (23955)------------------------------
% 0.22/0.54  % (23951)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (23951)Refutation not found, incomplete strategy% (23951)------------------------------
% 0.22/0.54  % (23951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23951)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23951)Memory used [KB]: 10618
% 0.22/0.54  % (23951)Time elapsed: 0.132 s
% 0.22/0.54  % (23951)------------------------------
% 0.22/0.54  % (23951)------------------------------
% 0.22/0.54  % (23941)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (23953)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (23967)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (23942)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (23953)Refutation not found, incomplete strategy% (23953)------------------------------
% 0.22/0.54  % (23953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23953)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23953)Memory used [KB]: 1663
% 0.22/0.54  % (23953)Time elapsed: 0.089 s
% 0.22/0.54  % (23953)------------------------------
% 0.22/0.54  % (23953)------------------------------
% 0.22/0.54  % (23962)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (23967)Refutation not found, incomplete strategy% (23967)------------------------------
% 0.22/0.55  % (23967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23967)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23967)Memory used [KB]: 10746
% 0.22/0.55  % (23967)Time elapsed: 0.128 s
% 0.22/0.55  % (23967)------------------------------
% 0.22/0.55  % (23967)------------------------------
% 0.22/0.55  % (23945)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (23954)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (23949)Refutation not found, incomplete strategy% (23949)------------------------------
% 0.22/0.55  % (23949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23949)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23949)Memory used [KB]: 10746
% 0.22/0.55  % (23949)Time elapsed: 0.135 s
% 0.22/0.55  % (23949)------------------------------
% 0.22/0.55  % (23949)------------------------------
% 0.22/0.55  % (23946)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (23968)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (23968)Refutation not found, incomplete strategy% (23968)------------------------------
% 0.22/0.55  % (23968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23968)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23968)Memory used [KB]: 1663
% 0.22/0.55  % (23968)Time elapsed: 0.138 s
% 0.22/0.55  % (23968)------------------------------
% 0.22/0.55  % (23968)------------------------------
% 0.22/0.55  % (23959)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (23958)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (23965)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (23965)Refutation not found, incomplete strategy% (23965)------------------------------
% 0.22/0.56  % (23965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23965)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23965)Memory used [KB]: 6268
% 0.22/0.56  % (23965)Time elapsed: 0.139 s
% 0.22/0.56  % (23965)------------------------------
% 0.22/0.56  % (23965)------------------------------
% 0.22/0.56  % (23964)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (23956)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (23956)Refutation not found, incomplete strategy% (23956)------------------------------
% 0.22/0.56  % (23956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23956)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23956)Memory used [KB]: 1663
% 0.22/0.56  % (23956)Time elapsed: 0.150 s
% 0.22/0.56  % (23956)------------------------------
% 0.22/0.56  % (23956)------------------------------
% 0.22/0.56  % (23952)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.07/0.64  % (23962)Refutation found. Thanks to Tanya!
% 2.07/0.64  % SZS status Theorem for theBenchmark
% 2.07/0.64  % SZS output start Proof for theBenchmark
% 2.07/0.64  fof(f1682,plain,(
% 2.07/0.64    $false),
% 2.07/0.64    inference(avatar_sat_refutation,[],[f86,f91,f1164,f1668,f1681])).
% 2.07/0.64  fof(f1681,plain,(
% 2.07/0.64    spl4_1 | ~spl4_10),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f1676])).
% 2.07/0.64  fof(f1676,plain,(
% 2.07/0.64    $false | (spl4_1 | ~spl4_10)),
% 2.07/0.64    inference(unit_resulting_resolution,[],[f85,f1163,f68])).
% 2.07/0.64  fof(f68,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.07/0.64    inference(definition_unfolding,[],[f41,f64])).
% 2.07/0.64  fof(f64,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.07/0.64    inference(definition_unfolding,[],[f56,f60])).
% 2.07/0.64  fof(f60,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f13])).
% 2.07/0.64  fof(f13,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.07/0.64  fof(f56,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f12])).
% 2.07/0.64  fof(f12,axiom,(
% 2.07/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.07/0.64  fof(f41,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f28])).
% 2.07/0.64  fof(f28,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.07/0.64    inference(flattening,[],[f27])).
% 2.07/0.64  fof(f27,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.07/0.64    inference(nnf_transformation,[],[f19])).
% 2.07/0.64  fof(f19,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.07/0.64  fof(f1163,plain,(
% 2.07/0.64    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_10),
% 2.07/0.64    inference(avatar_component_clause,[],[f1161])).
% 2.07/0.64  fof(f1161,plain,(
% 2.07/0.64    spl4_10 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.07/0.64  fof(f85,plain,(
% 2.07/0.64    ~r2_hidden(sK0,sK1) | spl4_1),
% 2.07/0.64    inference(avatar_component_clause,[],[f83])).
% 2.07/0.64  fof(f83,plain,(
% 2.07/0.64    spl4_1 <=> r2_hidden(sK0,sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.07/0.64  fof(f1668,plain,(
% 2.07/0.64    ~spl4_2 | spl4_8),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f1647])).
% 2.07/0.64  fof(f1647,plain,(
% 2.07/0.64    $false | (~spl4_2 | spl4_8)),
% 2.07/0.64    inference(unit_resulting_resolution,[],[f90,f899,f1284,f52])).
% 2.07/0.64  fof(f52,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f37])).
% 2.07/0.64  fof(f37,plain,(
% 2.07/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.64    inference(flattening,[],[f36])).
% 2.07/0.64  fof(f36,plain,(
% 2.07/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.64    inference(nnf_transformation,[],[f5])).
% 2.07/0.64  fof(f5,axiom,(
% 2.07/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.07/0.64  fof(f1284,plain,(
% 2.07/0.64    ( ! [X15,X16] : (r1_tarski(X16,k5_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(X16,X15))))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f1283,f238])).
% 2.07/0.64  fof(f238,plain,(
% 2.07/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.07/0.64    inference(forward_demodulation,[],[f225,f58])).
% 2.07/0.64  fof(f58,plain,(
% 2.07/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f7])).
% 2.07/0.64  fof(f7,axiom,(
% 2.07/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.07/0.64  fof(f225,plain,(
% 2.07/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 2.07/0.64    inference(superposition,[],[f138,f127])).
% 2.07/0.64  fof(f127,plain,(
% 2.07/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.07/0.64    inference(global_subsumption,[],[f117,f125])).
% 2.07/0.64  fof(f125,plain,(
% 2.07/0.64    ( ! [X0] : (r2_hidden(sK3(k5_xboole_0(X0,X0)),X0) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.07/0.64    inference(resolution,[],[f121,f49])).
% 2.07/0.64  fof(f49,plain,(
% 2.07/0.64    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f35])).
% 2.07/0.64  fof(f35,plain,(
% 2.07/0.64    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.07/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).
% 2.07/0.64  fof(f34,plain,(
% 2.07/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.07/0.64    introduced(choice_axiom,[])).
% 2.07/0.64  fof(f24,plain,(
% 2.07/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.07/0.64    inference(ennf_transformation,[],[f4])).
% 2.07/0.64  fof(f4,axiom,(
% 2.07/0.64    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.07/0.64  fof(f121,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 2.07/0.64    inference(superposition,[],[f79,f62])).
% 2.07/0.64  fof(f62,plain,(
% 2.07/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f22,plain,(
% 2.07/0.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.07/0.64    inference(rectify,[],[f3])).
% 2.07/0.64  fof(f3,axiom,(
% 2.07/0.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.07/0.64  fof(f79,plain,(
% 2.07/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 2.07/0.64    inference(equality_resolution,[],[f75])).
% 2.07/0.64  fof(f75,plain,(
% 2.07/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.07/0.64    inference(definition_unfolding,[],[f43,f57])).
% 2.07/0.64  fof(f57,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f6])).
% 2.07/0.64  fof(f6,axiom,(
% 2.07/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.07/0.64  fof(f43,plain,(
% 2.07/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.07/0.64    inference(cnf_transformation,[],[f33])).
% 2.07/0.64  fof(f33,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.07/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 2.07/0.64  fof(f32,plain,(
% 2.07/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.07/0.64    introduced(choice_axiom,[])).
% 2.07/0.64  fof(f31,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.07/0.64    inference(rectify,[],[f30])).
% 2.07/0.64  fof(f30,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.07/0.64    inference(flattening,[],[f29])).
% 2.07/0.64  fof(f29,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.07/0.64    inference(nnf_transformation,[],[f2])).
% 2.07/0.64  fof(f2,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.07/0.64  fof(f117,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(sK3(k5_xboole_0(X0,X0)),X0) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.07/0.64    inference(resolution,[],[f114,f49])).
% 2.07/0.64  fof(f114,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,X0)) )),
% 2.07/0.64    inference(superposition,[],[f78,f62])).
% 2.07/0.64  fof(f78,plain,(
% 2.07/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.07/0.64    inference(equality_resolution,[],[f74])).
% 2.07/0.64  fof(f74,plain,(
% 2.07/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.07/0.64    inference(definition_unfolding,[],[f44,f57])).
% 2.07/0.64  fof(f44,plain,(
% 2.07/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.07/0.64    inference(cnf_transformation,[],[f33])).
% 2.07/0.64  fof(f138,plain,(
% 2.07/0.64    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 2.07/0.64    inference(superposition,[],[f59,f127])).
% 2.07/0.64  fof(f59,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f9])).
% 2.07/0.64  fof(f9,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.07/0.64  fof(f1283,plain,(
% 2.07/0.64    ( ! [X15,X16] : (r1_tarski(k5_xboole_0(k1_xboole_0,X16),k5_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(k5_xboole_0(k1_xboole_0,X16),X15))))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f1282,f59])).
% 2.07/0.64  fof(f1282,plain,(
% 2.07/0.64    ( ! [X15,X16] : (r1_tarski(k5_xboole_0(k1_xboole_0,X16),k5_xboole_0(k5_xboole_0(X15,X16),k3_xboole_0(k5_xboole_0(k1_xboole_0,X16),X15)))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f1264,f631])).
% 2.07/0.64  fof(f631,plain,(
% 2.07/0.64    ( ! [X14,X13] : (k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13)) )),
% 2.07/0.64    inference(forward_demodulation,[],[f613,f238])).
% 2.07/0.64  fof(f613,plain,(
% 2.07/0.64    ( ! [X14,X13] : (k5_xboole_0(X13,X14) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X14),X13)) )),
% 2.07/0.64    inference(superposition,[],[f572,f138])).
% 2.07/0.64  fof(f572,plain,(
% 2.07/0.64    ( ! [X17,X18] : (k5_xboole_0(k5_xboole_0(X18,X17),X18) = X17) )),
% 2.07/0.64    inference(superposition,[],[f524,f524])).
% 2.07/0.64  fof(f524,plain,(
% 2.07/0.64    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3) )),
% 2.07/0.64    inference(superposition,[],[f499,f238])).
% 2.07/0.64  fof(f499,plain,(
% 2.07/0.64    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = X2) )),
% 2.07/0.64    inference(forward_demodulation,[],[f472,f58])).
% 2.07/0.64  fof(f472,plain,(
% 2.07/0.64    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 2.07/0.64    inference(superposition,[],[f138,f141])).
% 2.07/0.64  fof(f141,plain,(
% 2.07/0.64    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 2.07/0.64    inference(superposition,[],[f59,f127])).
% 2.07/0.64  fof(f1264,plain,(
% 2.07/0.64    ( ! [X15,X16] : (r1_tarski(k5_xboole_0(k1_xboole_0,X16),k5_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,X16),X15),k5_xboole_0(X15,X16)))) )),
% 2.07/0.64    inference(superposition,[],[f941,f137])).
% 2.07/0.64  fof(f137,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 2.07/0.64    inference(superposition,[],[f59,f58])).
% 2.07/0.64  fof(f941,plain,(
% 2.07/0.64    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(k3_xboole_0(X23,X24),k5_xboole_0(X24,X23)))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f919,f631])).
% 2.07/0.64  fof(f919,plain,(
% 2.07/0.64    ( ! [X24,X23] : (r1_tarski(X23,k5_xboole_0(k5_xboole_0(X24,X23),k3_xboole_0(X23,X24)))) )),
% 2.07/0.64    inference(superposition,[],[f794,f524])).
% 2.07/0.64  fof(f794,plain,(
% 2.07/0.64    ( ! [X2,X3] : (r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X2,k5_xboole_0(X2,X3))))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f793,f61])).
% 2.07/0.64  fof(f61,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f1])).
% 2.07/0.64  fof(f1,axiom,(
% 2.07/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.07/0.64  fof(f793,plain,(
% 2.07/0.64    ( ! [X2,X3] : (r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X2,X3),X2)))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f758,f238])).
% 2.07/0.64  fof(f758,plain,(
% 2.07/0.64    ( ! [X2,X3] : (r1_tarski(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X2,X3),X2))))) )),
% 2.07/0.64    inference(superposition,[],[f148,f138])).
% 2.07/0.64  fof(f148,plain,(
% 2.07/0.64    ( ! [X19,X20,X18] : (r1_tarski(X20,k5_xboole_0(X20,k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(k5_xboole_0(X18,X19),X20)))))) )),
% 2.07/0.64    inference(superposition,[],[f76,f59])).
% 2.07/0.64  fof(f76,plain,(
% 2.07/0.64    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.07/0.64    inference(definition_unfolding,[],[f53,f63])).
% 2.07/0.64  fof(f63,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.07/0.64    inference(definition_unfolding,[],[f54,f57])).
% 2.07/0.64  fof(f54,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f10])).
% 2.07/0.64  fof(f10,axiom,(
% 2.07/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.07/0.64  fof(f53,plain,(
% 2.07/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f8])).
% 2.07/0.64  fof(f8,axiom,(
% 2.07/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.07/0.64  fof(f899,plain,(
% 2.07/0.64    sK1 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) | spl4_8),
% 2.07/0.64    inference(avatar_component_clause,[],[f898])).
% 2.07/0.64  fof(f898,plain,(
% 2.07/0.64    spl4_8 <=> sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.07/0.64  fof(f90,plain,(
% 2.07/0.64    r1_tarski(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),sK1) | ~spl4_2),
% 2.07/0.64    inference(avatar_component_clause,[],[f88])).
% 2.07/0.64  fof(f88,plain,(
% 2.07/0.64    spl4_2 <=> r1_tarski(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.07/0.64  fof(f1164,plain,(
% 2.07/0.64    spl4_10 | ~spl4_8),
% 2.07/0.64    inference(avatar_split_clause,[],[f1132,f898,f1161])).
% 2.07/0.64  fof(f1132,plain,(
% 2.07/0.64    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_8),
% 2.07/0.64    inference(superposition,[],[f76,f900])).
% 2.07/0.64  fof(f900,plain,(
% 2.07/0.64    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) | ~spl4_8),
% 2.07/0.64    inference(avatar_component_clause,[],[f898])).
% 2.07/0.64  fof(f91,plain,(
% 2.07/0.64    spl4_2),
% 2.07/0.64    inference(avatar_split_clause,[],[f66,f88])).
% 2.07/0.64  fof(f66,plain,(
% 2.07/0.64    r1_tarski(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),sK1)),
% 2.07/0.64    inference(definition_unfolding,[],[f38,f63,f65])).
% 2.07/0.64  fof(f65,plain,(
% 2.07/0.64    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.07/0.64    inference(definition_unfolding,[],[f55,f64])).
% 2.07/0.64  fof(f55,plain,(
% 2.07/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f11])).
% 2.07/0.64  fof(f11,axiom,(
% 2.07/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.07/0.64  fof(f38,plain,(
% 2.07/0.64    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.07/0.64    inference(cnf_transformation,[],[f26])).
% 2.07/0.64  fof(f26,plain,(
% 2.07/0.64    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.07/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).
% 2.07/0.64  fof(f25,plain,(
% 2.07/0.64    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 2.07/0.64    introduced(choice_axiom,[])).
% 2.07/0.64  fof(f23,plain,(
% 2.07/0.64    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f21])).
% 2.07/0.64  fof(f21,negated_conjecture,(
% 2.07/0.64    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.07/0.64    inference(negated_conjecture,[],[f20])).
% 2.07/0.64  fof(f20,conjecture,(
% 2.07/0.64    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 2.07/0.64  fof(f86,plain,(
% 2.07/0.64    ~spl4_1),
% 2.07/0.64    inference(avatar_split_clause,[],[f39,f83])).
% 2.07/0.64  fof(f39,plain,(
% 2.07/0.64    ~r2_hidden(sK0,sK1)),
% 2.07/0.64    inference(cnf_transformation,[],[f26])).
% 2.07/0.64  % SZS output end Proof for theBenchmark
% 2.07/0.64  % (23962)------------------------------
% 2.07/0.64  % (23962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (23962)Termination reason: Refutation
% 2.07/0.64  
% 2.07/0.64  % (23962)Memory used [KB]: 11769
% 2.07/0.64  % (23962)Time elapsed: 0.220 s
% 2.07/0.64  % (23962)------------------------------
% 2.07/0.64  % (23962)------------------------------
% 2.07/0.65  % (23938)Success in time 0.27 s
%------------------------------------------------------------------------------
