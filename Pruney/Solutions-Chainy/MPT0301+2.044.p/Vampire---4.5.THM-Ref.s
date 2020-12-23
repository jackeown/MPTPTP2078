%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:58 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 645 expanded)
%              Number of leaves         :   19 ( 172 expanded)
%              Depth                    :   22
%              Number of atoms          :  347 (2361 expanded)
%              Number of equality atoms :   98 ( 428 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f596,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f81,f509,f520,f535,f572,f595])).

fof(f595,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f589,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK0
    | spl6_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f589,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_4 ),
    inference(superposition,[],[f91,f581])).

fof(f581,plain,
    ( ! [X3] : sK0 = k3_xboole_0(sK0,X3)
    | ~ spl6_4 ),
    inference(resolution,[],[f576,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f576,plain,
    ( ! [X6] : r1_tarski(sK0,X6)
    | ~ spl6_4 ),
    inference(resolution,[],[f531,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f531,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl6_4
  <=> ! [X4] : ~ r2_hidden(X4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f91,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f44,f87])).

fof(f87,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f83,f86])).

fof(f86,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f572,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f566,f74])).

fof(f74,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f566,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(superposition,[],[f91,f547])).

fof(f547,plain,
    ( ! [X3] : sK1 = k3_xboole_0(sK1,X3)
    | ~ spl6_5 ),
    inference(resolution,[],[f543,f40])).

fof(f543,plain,
    ( ! [X6] : r1_tarski(sK1,X6)
    | ~ spl6_5 ),
    inference(resolution,[],[f534,f42])).

fof(f534,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl6_5
  <=> ! [X5] : ~ r2_hidden(X5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f535,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f528,f68,f533,f530])).

fof(f68,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f528,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f523,f267])).

fof(f267,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f259,f37])).

fof(f259,plain,(
    ! [X1] : ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f252,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f92,f44])).

fof(f92,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f38,f91])).

fof(f252,plain,(
    ! [X4,X7] : ~ r2_hidden(X4,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7))) ),
    inference(condensation,[],[f248])).

fof(f248,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k5_xboole_0(X5,k3_xboole_0(X5,X6)))
      | ~ r2_hidden(X4,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7))) ) ),
    inference(resolution,[],[f240,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0))) ) ),
    inference(forward_demodulation,[],[f231,f37])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0))) ) ),
    inference(superposition,[],[f127,f86])).

fof(f127,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_hidden(X13,k5_xboole_0(X14,k3_xboole_0(X14,X15)))
      | ~ r2_hidden(X13,k5_xboole_0(X16,k3_xboole_0(X16,X14))) ) ),
    inference(resolution,[],[f66,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f523,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k1_xboole_0)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f54,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f520,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f518,f345])).

fof(f345,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f307,f91])).

fof(f307,plain,(
    ! [X4,X5] : k2_zfmisc_1(k1_xboole_0,X4) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X4),X5) ),
    inference(resolution,[],[f294,f40])).

fof(f294,plain,(
    ! [X12,X13] : r1_tarski(k2_zfmisc_1(k1_xboole_0,X12),X13) ),
    inference(resolution,[],[f279,f42])).

fof(f279,plain,(
    ! [X8,X7] : ~ r2_hidden(X7,k2_zfmisc_1(k1_xboole_0,X8)) ),
    inference(resolution,[],[f267,f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X2,X0,X1,X0,X1),X0)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(forward_demodulation,[],[f212,f86])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK4(X2,X0,X1,X0,X1),k3_xboole_0(X0,X0)) ) ),
    inference(superposition,[],[f56,f86])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK4(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK4(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4)) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f32])).

fof(f32,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
     => ( r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK4(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f518,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f70,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f70,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f509,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f507])).

fof(f507,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f82,f480])).

fof(f480,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0) ),
    inference(superposition,[],[f435,f91])).

fof(f435,plain,(
    ! [X4,X5] : k2_zfmisc_1(X4,k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X4,k1_xboole_0),X5) ),
    inference(resolution,[],[f429,f40])).

fof(f429,plain,(
    ! [X12,X13] : r1_tarski(k2_zfmisc_1(X12,k1_xboole_0),X13) ),
    inference(resolution,[],[f422,f42])).

fof(f422,plain,(
    ! [X21,X20] : ~ r2_hidden(X20,k2_zfmisc_1(X21,k1_xboole_0)) ),
    inference(resolution,[],[f289,f267])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X2,X0,X1,X0,X1),X1)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(forward_demodulation,[],[f288,f86])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK5(X2,X0,X1,X0,X1),k3_xboole_0(X1,X1)) ) ),
    inference(superposition,[],[f57,f86])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f70,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f81,plain,
    ( spl6_1
    | spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f34,f72,f77,f68])).

fof(f34,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f80,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f35,f77,f68])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f36,f72,f68])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.25  % Computer   : n010.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % WCLimit    : 600
% 0.07/0.25  % DateTime   : Tue Dec  1 13:06:59 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.10/0.34  % (16921)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.10/0.34  % (16924)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.10/0.34  % (16913)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.10/0.34  % (16921)Refutation not found, incomplete strategy% (16921)------------------------------
% 0.10/0.34  % (16921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.35  % (16921)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.35  
% 0.10/0.35  % (16921)Memory used [KB]: 10618
% 0.10/0.35  % (16921)Time elapsed: 0.050 s
% 0.10/0.35  % (16921)------------------------------
% 0.10/0.35  % (16921)------------------------------
% 0.10/0.35  % (16922)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.10/0.35  % (16934)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.10/0.35  % (16922)Refutation not found, incomplete strategy% (16922)------------------------------
% 0.10/0.35  % (16922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.35  % (16922)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.35  
% 0.10/0.35  % (16922)Memory used [KB]: 10618
% 0.10/0.35  % (16922)Time elapsed: 0.057 s
% 0.10/0.35  % (16922)------------------------------
% 0.10/0.35  % (16922)------------------------------
% 0.10/0.36  % (16913)Refutation not found, incomplete strategy% (16913)------------------------------
% 0.10/0.36  % (16913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.36  % (16913)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.36  
% 0.10/0.36  % (16913)Memory used [KB]: 10618
% 0.10/0.36  % (16913)Time elapsed: 0.057 s
% 0.10/0.36  % (16913)------------------------------
% 0.10/0.36  % (16913)------------------------------
% 0.10/0.36  % (16938)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.10/0.36  % (16938)Refutation not found, incomplete strategy% (16938)------------------------------
% 0.10/0.36  % (16938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.36  % (16938)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.36  
% 0.10/0.36  % (16938)Memory used [KB]: 10618
% 0.10/0.36  % (16938)Time elapsed: 0.068 s
% 0.10/0.36  % (16938)------------------------------
% 0.10/0.36  % (16938)------------------------------
% 0.10/0.36  % (16918)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.10/0.36  % (16914)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.10/0.36  % (16920)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.10/0.36  % (16915)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.10/0.36  % (16920)Refutation not found, incomplete strategy% (16920)------------------------------
% 0.10/0.36  % (16920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.36  % (16920)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.36  
% 0.10/0.36  % (16920)Memory used [KB]: 10618
% 0.10/0.36  % (16920)Time elapsed: 0.067 s
% 0.10/0.36  % (16920)------------------------------
% 0.10/0.36  % (16920)------------------------------
% 0.10/0.37  % (16911)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.10/0.37  % (16915)Refutation not found, incomplete strategy% (16915)------------------------------
% 0.10/0.37  % (16915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.37  % (16915)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.37  
% 0.10/0.37  % (16915)Memory used [KB]: 6140
% 0.10/0.37  % (16915)Time elapsed: 0.067 s
% 0.10/0.37  % (16915)------------------------------
% 0.10/0.37  % (16915)------------------------------
% 0.10/0.37  % (16923)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.10/0.37  % (16926)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.10/0.37  % (16939)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.10/0.37  % (16911)Refutation not found, incomplete strategy% (16911)------------------------------
% 0.10/0.37  % (16911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.37  % (16911)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.37  
% 0.10/0.37  % (16911)Memory used [KB]: 1663
% 0.10/0.37  % (16911)Time elapsed: 0.077 s
% 0.10/0.37  % (16911)------------------------------
% 0.10/0.37  % (16911)------------------------------
% 0.10/0.37  % (16926)Refutation not found, incomplete strategy% (16926)------------------------------
% 0.10/0.37  % (16926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.37  % (16926)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.37  
% 0.10/0.37  % (16926)Memory used [KB]: 6140
% 0.10/0.37  % (16926)Time elapsed: 0.004 s
% 0.10/0.37  % (16926)------------------------------
% 0.10/0.37  % (16926)------------------------------
% 0.10/0.37  % (16916)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.10/0.38  % (16912)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.10/0.38  % (16941)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.10/0.38  % (16917)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.10/0.39  % (16933)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.10/0.39  % (16940)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.10/0.39  % (16919)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.10/0.39  % (16932)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.10/0.39  % (16928)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.10/0.39  % (16932)Refutation not found, incomplete strategy% (16932)------------------------------
% 0.10/0.39  % (16932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.40  % (16930)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.10/0.40  % (16919)Refutation not found, incomplete strategy% (16919)------------------------------
% 0.10/0.40  % (16919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.40  % (16919)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.40  
% 0.10/0.40  % (16919)Memory used [KB]: 10618
% 0.10/0.40  % (16919)Time elapsed: 0.106 s
% 0.10/0.40  % (16919)------------------------------
% 0.10/0.40  % (16919)------------------------------
% 0.10/0.40  % (16936)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.10/0.40  % (16927)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.10/0.40  % (16931)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.10/0.40  % (16931)Refutation not found, incomplete strategy% (16931)------------------------------
% 0.10/0.40  % (16931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.40  % (16931)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.40  
% 0.10/0.40  % (16931)Memory used [KB]: 10746
% 0.10/0.40  % (16931)Time elapsed: 0.107 s
% 0.10/0.40  % (16931)------------------------------
% 0.10/0.40  % (16931)------------------------------
% 0.10/0.41  % (16929)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.10/0.41  % (16928)Refutation not found, incomplete strategy% (16928)------------------------------
% 0.10/0.41  % (16928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.41  % (16928)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.41  
% 0.10/0.41  % (16928)Memory used [KB]: 10618
% 0.10/0.41  % (16928)Time elapsed: 0.114 s
% 0.10/0.41  % (16928)------------------------------
% 0.10/0.41  % (16928)------------------------------
% 0.10/0.41  % (16925)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.10/0.41  % (16932)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.41  
% 0.10/0.41  % (16932)Memory used [KB]: 1663
% 0.10/0.41  % (16932)Time elapsed: 0.098 s
% 0.10/0.41  % (16932)------------------------------
% 0.10/0.41  % (16932)------------------------------
% 0.10/0.42  % (16937)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.10/0.42  % (16937)Refutation not found, incomplete strategy% (16937)------------------------------
% 0.10/0.42  % (16937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (16937)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.42  
% 0.10/0.42  % (16937)Memory used [KB]: 6140
% 0.10/0.42  % (16937)Time elapsed: 0.125 s
% 0.10/0.42  % (16937)------------------------------
% 0.10/0.42  % (16937)------------------------------
% 0.10/0.42  % (16914)Refutation found. Thanks to Tanya!
% 0.10/0.42  % SZS status Theorem for theBenchmark
% 0.10/0.42  % SZS output start Proof for theBenchmark
% 0.10/0.42  fof(f596,plain,(
% 0.10/0.42    $false),
% 0.10/0.42    inference(avatar_sat_refutation,[],[f75,f80,f81,f509,f520,f535,f572,f595])).
% 0.10/0.42  fof(f595,plain,(
% 0.10/0.42    spl6_3 | ~spl6_4),
% 0.10/0.42    inference(avatar_contradiction_clause,[],[f594])).
% 0.10/0.42  fof(f594,plain,(
% 0.10/0.42    $false | (spl6_3 | ~spl6_4)),
% 0.10/0.42    inference(subsumption_resolution,[],[f589,f79])).
% 0.10/0.42  fof(f79,plain,(
% 0.10/0.42    k1_xboole_0 != sK0 | spl6_3),
% 0.10/0.42    inference(avatar_component_clause,[],[f77])).
% 0.10/0.42  fof(f77,plain,(
% 0.10/0.42    spl6_3 <=> k1_xboole_0 = sK0),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.10/0.42  fof(f589,plain,(
% 0.10/0.42    k1_xboole_0 = sK0 | ~spl6_4),
% 0.10/0.42    inference(superposition,[],[f91,f581])).
% 0.10/0.42  fof(f581,plain,(
% 0.10/0.42    ( ! [X3] : (sK0 = k3_xboole_0(sK0,X3)) ) | ~spl6_4),
% 0.10/0.42    inference(resolution,[],[f576,f40])).
% 0.10/0.42  fof(f40,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.10/0.42    inference(cnf_transformation,[],[f13])).
% 0.10/0.42  fof(f13,plain,(
% 0.10/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.10/0.42    inference(ennf_transformation,[],[f6])).
% 0.10/0.42  fof(f6,axiom,(
% 0.10/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.10/0.42  fof(f576,plain,(
% 0.10/0.42    ( ! [X6] : (r1_tarski(sK0,X6)) ) | ~spl6_4),
% 0.10/0.42    inference(resolution,[],[f531,f42])).
% 0.10/0.42  fof(f42,plain,(
% 0.10/0.42    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f23])).
% 0.10/0.42  fof(f23,plain,(
% 0.10/0.42    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.10/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.10/0.42  fof(f22,plain,(
% 0.10/0.42    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.10/0.42    introduced(choice_axiom,[])).
% 0.10/0.42  fof(f21,plain,(
% 0.10/0.42    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.10/0.42    inference(rectify,[],[f20])).
% 0.10/0.42  fof(f20,plain,(
% 0.10/0.42    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.10/0.42    inference(nnf_transformation,[],[f14])).
% 0.10/0.42  fof(f14,plain,(
% 0.10/0.42    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.10/0.42    inference(ennf_transformation,[],[f1])).
% 0.10/0.42  fof(f1,axiom,(
% 0.10/0.42    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.10/0.42  fof(f531,plain,(
% 0.10/0.42    ( ! [X4] : (~r2_hidden(X4,sK0)) ) | ~spl6_4),
% 0.10/0.42    inference(avatar_component_clause,[],[f530])).
% 0.10/0.42  fof(f530,plain,(
% 0.10/0.42    spl6_4 <=> ! [X4] : ~r2_hidden(X4,sK0)),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.10/0.42  fof(f91,plain,(
% 0.10/0.42    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 0.10/0.42    inference(resolution,[],[f44,f87])).
% 0.10/0.42  fof(f87,plain,(
% 0.10/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.10/0.42    inference(backward_demodulation,[],[f83,f86])).
% 0.10/0.42  fof(f86,plain,(
% 0.10/0.42    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.10/0.42    inference(resolution,[],[f85,f40])).
% 0.10/0.42  fof(f85,plain,(
% 0.10/0.42    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.10/0.42    inference(duplicate_literal_removal,[],[f84])).
% 0.10/0.42  fof(f84,plain,(
% 0.10/0.42    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.10/0.42    inference(resolution,[],[f43,f42])).
% 0.10/0.42  fof(f43,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f23])).
% 0.10/0.42  fof(f83,plain,(
% 0.10/0.42    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) )),
% 0.10/0.42    inference(superposition,[],[f38,f37])).
% 0.10/0.42  fof(f37,plain,(
% 0.10/0.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f7])).
% 0.10/0.42  fof(f7,axiom,(
% 0.10/0.42    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.10/0.42  fof(f38,plain,(
% 0.10/0.42    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.10/0.42    inference(cnf_transformation,[],[f5])).
% 0.10/0.42  fof(f5,axiom,(
% 0.10/0.42    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).
% 0.10/0.42  fof(f44,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.10/0.42    inference(cnf_transformation,[],[f24])).
% 0.10/0.42  fof(f24,plain,(
% 0.10/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.10/0.42    inference(nnf_transformation,[],[f3])).
% 0.10/0.42  fof(f3,axiom,(
% 0.10/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.10/0.42  fof(f572,plain,(
% 0.10/0.42    spl6_2 | ~spl6_5),
% 0.10/0.42    inference(avatar_contradiction_clause,[],[f571])).
% 0.10/0.42  fof(f571,plain,(
% 0.10/0.42    $false | (spl6_2 | ~spl6_5)),
% 0.10/0.42    inference(subsumption_resolution,[],[f566,f74])).
% 0.10/0.42  fof(f74,plain,(
% 0.10/0.42    k1_xboole_0 != sK1 | spl6_2),
% 0.10/0.42    inference(avatar_component_clause,[],[f72])).
% 0.10/0.42  fof(f72,plain,(
% 0.10/0.42    spl6_2 <=> k1_xboole_0 = sK1),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.10/0.42  fof(f566,plain,(
% 0.10/0.42    k1_xboole_0 = sK1 | ~spl6_5),
% 0.10/0.42    inference(superposition,[],[f91,f547])).
% 0.10/0.42  fof(f547,plain,(
% 0.10/0.42    ( ! [X3] : (sK1 = k3_xboole_0(sK1,X3)) ) | ~spl6_5),
% 0.10/0.42    inference(resolution,[],[f543,f40])).
% 0.10/0.42  fof(f543,plain,(
% 0.10/0.42    ( ! [X6] : (r1_tarski(sK1,X6)) ) | ~spl6_5),
% 0.10/0.42    inference(resolution,[],[f534,f42])).
% 0.10/0.42  fof(f534,plain,(
% 0.10/0.42    ( ! [X5] : (~r2_hidden(X5,sK1)) ) | ~spl6_5),
% 0.10/0.42    inference(avatar_component_clause,[],[f533])).
% 0.10/0.42  fof(f533,plain,(
% 0.10/0.42    spl6_5 <=> ! [X5] : ~r2_hidden(X5,sK1)),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.10/0.42  fof(f535,plain,(
% 0.10/0.42    spl6_4 | spl6_5 | ~spl6_1),
% 0.10/0.42    inference(avatar_split_clause,[],[f528,f68,f533,f530])).
% 0.10/0.42  fof(f68,plain,(
% 0.10/0.42    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.10/0.42  fof(f528,plain,(
% 0.10/0.42    ( ! [X4,X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK0)) ) | ~spl6_1),
% 0.10/0.42    inference(subsumption_resolution,[],[f523,f267])).
% 0.10/0.42  fof(f267,plain,(
% 0.10/0.42    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.10/0.42    inference(forward_demodulation,[],[f259,f37])).
% 0.10/0.42  fof(f259,plain,(
% 0.10/0.42    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.10/0.42    inference(superposition,[],[f252,f93])).
% 0.10/0.42  fof(f93,plain,(
% 0.10/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.10/0.42    inference(resolution,[],[f92,f44])).
% 0.10/0.42  fof(f92,plain,(
% 0.10/0.42    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.10/0.42    inference(superposition,[],[f38,f91])).
% 0.10/0.42  fof(f252,plain,(
% 0.10/0.42    ( ! [X4,X7] : (~r2_hidden(X4,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)))) )),
% 0.10/0.42    inference(condensation,[],[f248])).
% 0.10/0.42  fof(f248,plain,(
% 0.10/0.42    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k5_xboole_0(X5,k3_xboole_0(X5,X6))) | ~r2_hidden(X4,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)))) )),
% 0.10/0.42    inference(resolution,[],[f240,f66])).
% 0.10/0.42  fof(f66,plain,(
% 0.10/0.42    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.10/0.42    inference(equality_resolution,[],[f63])).
% 0.10/0.42  fof(f63,plain,(
% 0.10/0.42    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.10/0.42    inference(definition_unfolding,[],[f46,f39])).
% 0.10/0.42  fof(f39,plain,(
% 0.10/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.10/0.42    inference(cnf_transformation,[],[f4])).
% 0.10/0.42  fof(f4,axiom,(
% 0.10/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.10/0.42  fof(f46,plain,(
% 0.10/0.42    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.10/0.42    inference(cnf_transformation,[],[f29])).
% 0.10/0.42  fof(f29,plain,(
% 0.10/0.42    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.10/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.10/0.42  fof(f28,plain,(
% 0.10/0.42    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.10/0.42    introduced(choice_axiom,[])).
% 0.10/0.42  fof(f27,plain,(
% 0.10/0.42    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.10/0.42    inference(rectify,[],[f26])).
% 0.10/0.42  fof(f26,plain,(
% 0.10/0.42    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.10/0.42    inference(flattening,[],[f25])).
% 0.10/0.42  fof(f25,plain,(
% 0.10/0.42    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.10/0.42    inference(nnf_transformation,[],[f2])).
% 0.10/0.42  fof(f2,axiom,(
% 0.10/0.42    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.10/0.42  fof(f240,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) )),
% 0.10/0.42    inference(forward_demodulation,[],[f231,f37])).
% 0.10/0.42  fof(f231,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) )),
% 0.10/0.42    inference(superposition,[],[f127,f86])).
% 0.10/0.42  fof(f127,plain,(
% 0.10/0.42    ( ! [X14,X15,X13,X16] : (~r2_hidden(X13,k5_xboole_0(X14,k3_xboole_0(X14,X15))) | ~r2_hidden(X13,k5_xboole_0(X16,k3_xboole_0(X16,X14)))) )),
% 0.10/0.42    inference(resolution,[],[f66,f65])).
% 0.10/0.42  fof(f65,plain,(
% 0.10/0.42    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.10/0.42    inference(equality_resolution,[],[f62])).
% 0.10/0.42  fof(f62,plain,(
% 0.10/0.42    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.10/0.42    inference(definition_unfolding,[],[f47,f39])).
% 0.10/0.42  fof(f47,plain,(
% 0.10/0.42    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.10/0.42    inference(cnf_transformation,[],[f29])).
% 0.10/0.42  fof(f523,plain,(
% 0.10/0.42    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k1_xboole_0) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK0)) ) | ~spl6_1),
% 0.10/0.42    inference(superposition,[],[f54,f69])).
% 0.10/0.42  fof(f69,plain,(
% 0.10/0.42    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_1),
% 0.10/0.42    inference(avatar_component_clause,[],[f68])).
% 0.10/0.42  fof(f54,plain,(
% 0.10/0.42    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f31])).
% 0.10/0.42  fof(f31,plain,(
% 0.10/0.42    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.10/0.42    inference(flattening,[],[f30])).
% 0.10/0.42  fof(f30,plain,(
% 0.10/0.42    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.10/0.42    inference(nnf_transformation,[],[f9])).
% 0.10/0.42  fof(f9,axiom,(
% 0.10/0.42    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.10/0.42  fof(f520,plain,(
% 0.10/0.42    spl6_1 | ~spl6_3),
% 0.10/0.42    inference(avatar_contradiction_clause,[],[f519])).
% 0.10/0.42  fof(f519,plain,(
% 0.10/0.42    $false | (spl6_1 | ~spl6_3)),
% 0.10/0.42    inference(subsumption_resolution,[],[f518,f345])).
% 0.10/0.42  fof(f345,plain,(
% 0.10/0.42    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 0.10/0.42    inference(superposition,[],[f307,f91])).
% 0.10/0.42  fof(f307,plain,(
% 0.10/0.42    ( ! [X4,X5] : (k2_zfmisc_1(k1_xboole_0,X4) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X4),X5)) )),
% 0.10/0.42    inference(resolution,[],[f294,f40])).
% 0.10/0.42  fof(f294,plain,(
% 0.10/0.42    ( ! [X12,X13] : (r1_tarski(k2_zfmisc_1(k1_xboole_0,X12),X13)) )),
% 0.10/0.42    inference(resolution,[],[f279,f42])).
% 0.10/0.42  fof(f279,plain,(
% 0.10/0.42    ( ! [X8,X7] : (~r2_hidden(X7,k2_zfmisc_1(k1_xboole_0,X8))) )),
% 0.10/0.42    inference(resolution,[],[f267,f213])).
% 0.10/0.42  fof(f213,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (r2_hidden(sK4(X2,X0,X1,X0,X1),X0) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 0.10/0.42    inference(forward_demodulation,[],[f212,f86])).
% 0.10/0.42  fof(f212,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | r2_hidden(sK4(X2,X0,X1,X0,X1),k3_xboole_0(X0,X0))) )),
% 0.10/0.42    inference(superposition,[],[f56,f86])).
% 0.10/0.42  fof(f56,plain,(
% 0.10/0.42    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK4(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))) )),
% 0.10/0.42    inference(cnf_transformation,[],[f33])).
% 0.10/0.42  fof(f33,plain,(
% 0.10/0.42    ! [X0,X1,X2,X3,X4] : ((r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) & r2_hidden(sK4(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) & k4_tarski(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4)) = X0) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.10/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f32])).
% 0.10/0.42  fof(f32,plain,(
% 0.10/0.42    ! [X4,X3,X2,X1,X0] : (? [X5,X6] : (r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) => (r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) & r2_hidden(sK4(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) & k4_tarski(sK4(X0,X1,X2,X3,X4),sK5(X0,X1,X2,X3,X4)) = X0))),
% 0.10/0.42    introduced(choice_axiom,[])).
% 0.10/0.42  fof(f15,plain,(
% 0.10/0.42    ! [X0,X1,X2,X3,X4] : (? [X5,X6] : (r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.10/0.42    inference(ennf_transformation,[],[f8])).
% 0.10/0.42  fof(f8,axiom,(
% 0.10/0.42    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).
% 0.10/0.42  fof(f518,plain,(
% 0.10/0.42    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl6_1 | ~spl6_3)),
% 0.10/0.42    inference(forward_demodulation,[],[f70,f78])).
% 0.10/0.42  fof(f78,plain,(
% 0.10/0.42    k1_xboole_0 = sK0 | ~spl6_3),
% 0.10/0.42    inference(avatar_component_clause,[],[f77])).
% 0.10/0.42  fof(f70,plain,(
% 0.10/0.42    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl6_1),
% 0.10/0.42    inference(avatar_component_clause,[],[f68])).
% 0.10/0.42  fof(f509,plain,(
% 0.10/0.42    spl6_1 | ~spl6_2),
% 0.10/0.42    inference(avatar_contradiction_clause,[],[f508])).
% 0.10/0.42  fof(f508,plain,(
% 0.10/0.42    $false | (spl6_1 | ~spl6_2)),
% 0.10/0.42    inference(trivial_inequality_removal,[],[f507])).
% 0.10/0.42  fof(f507,plain,(
% 0.10/0.42    k1_xboole_0 != k1_xboole_0 | (spl6_1 | ~spl6_2)),
% 0.10/0.42    inference(superposition,[],[f82,f480])).
% 0.10/0.42  fof(f480,plain,(
% 0.10/0.42    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0)) )),
% 0.10/0.42    inference(superposition,[],[f435,f91])).
% 0.10/0.42  fof(f435,plain,(
% 0.10/0.42    ( ! [X4,X5] : (k2_zfmisc_1(X4,k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X4,k1_xboole_0),X5)) )),
% 0.10/0.42    inference(resolution,[],[f429,f40])).
% 0.10/0.42  fof(f429,plain,(
% 0.10/0.42    ( ! [X12,X13] : (r1_tarski(k2_zfmisc_1(X12,k1_xboole_0),X13)) )),
% 0.10/0.42    inference(resolution,[],[f422,f42])).
% 0.10/0.42  fof(f422,plain,(
% 0.10/0.42    ( ! [X21,X20] : (~r2_hidden(X20,k2_zfmisc_1(X21,k1_xboole_0))) )),
% 0.10/0.42    inference(resolution,[],[f289,f267])).
% 0.10/0.42  fof(f289,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (r2_hidden(sK5(X2,X0,X1,X0,X1),X1) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 0.10/0.42    inference(forward_demodulation,[],[f288,f86])).
% 0.10/0.42  fof(f288,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | r2_hidden(sK5(X2,X0,X1,X0,X1),k3_xboole_0(X1,X1))) )),
% 0.10/0.42    inference(superposition,[],[f57,f86])).
% 0.10/0.42  fof(f57,plain,(
% 0.10/0.42    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))) )),
% 0.10/0.42    inference(cnf_transformation,[],[f33])).
% 0.10/0.42  fof(f82,plain,(
% 0.10/0.42    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl6_1 | ~spl6_2)),
% 0.10/0.42    inference(forward_demodulation,[],[f70,f73])).
% 0.10/0.42  fof(f73,plain,(
% 0.10/0.42    k1_xboole_0 = sK1 | ~spl6_2),
% 0.10/0.42    inference(avatar_component_clause,[],[f72])).
% 0.10/0.42  fof(f81,plain,(
% 0.10/0.42    spl6_1 | spl6_3 | spl6_2),
% 0.10/0.42    inference(avatar_split_clause,[],[f34,f72,f77,f68])).
% 0.10/0.42  fof(f34,plain,(
% 0.10/0.42    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.10/0.42    inference(cnf_transformation,[],[f19])).
% 0.10/0.42  fof(f19,plain,(
% 0.10/0.42    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.10/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 0.10/0.42  fof(f18,plain,(
% 0.10/0.42    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.10/0.42    introduced(choice_axiom,[])).
% 0.10/0.42  fof(f17,plain,(
% 0.10/0.42    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.10/0.42    inference(flattening,[],[f16])).
% 0.10/0.42  fof(f16,plain,(
% 0.10/0.42    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.10/0.42    inference(nnf_transformation,[],[f12])).
% 0.10/0.42  fof(f12,plain,(
% 0.10/0.42    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.10/0.42    inference(ennf_transformation,[],[f11])).
% 0.10/0.42  fof(f11,negated_conjecture,(
% 0.10/0.42    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.10/0.42    inference(negated_conjecture,[],[f10])).
% 0.10/0.42  fof(f10,conjecture,(
% 0.10/0.42    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.10/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.10/0.42  fof(f80,plain,(
% 0.10/0.42    ~spl6_1 | ~spl6_3),
% 0.10/0.42    inference(avatar_split_clause,[],[f35,f77,f68])).
% 0.10/0.42  fof(f35,plain,(
% 0.10/0.42    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.10/0.42    inference(cnf_transformation,[],[f19])).
% 0.10/0.42  fof(f75,plain,(
% 0.10/0.42    ~spl6_1 | ~spl6_2),
% 0.10/0.42    inference(avatar_split_clause,[],[f36,f72,f68])).
% 0.10/0.42  fof(f36,plain,(
% 0.10/0.42    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.10/0.42    inference(cnf_transformation,[],[f19])).
% 0.10/0.42  % SZS output end Proof for theBenchmark
% 0.10/0.42  % (16914)------------------------------
% 0.10/0.42  % (16914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (16914)Termination reason: Refutation
% 0.10/0.42  
% 0.10/0.42  % (16914)Memory used [KB]: 11129
% 0.10/0.42  % (16914)Time elapsed: 0.130 s
% 0.10/0.42  % (16914)------------------------------
% 0.10/0.42  % (16914)------------------------------
% 0.10/0.42  % (16909)Success in time 0.152 s
%------------------------------------------------------------------------------
