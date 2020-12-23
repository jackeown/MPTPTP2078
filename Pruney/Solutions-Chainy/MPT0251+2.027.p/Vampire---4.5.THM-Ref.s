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
% DateTime   : Thu Dec  3 12:38:38 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 595 expanded)
%              Number of leaves         :   23 ( 196 expanded)
%              Depth                    :   21
%              Number of atoms          :  290 (1191 expanded)
%              Number of equality atoms :   88 ( 586 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f649,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f93,f98,f204,f648])).

fof(f648,plain,
    ( ~ spl4_2
    | spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f647,f202,f96,f91])).

fof(f91,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f96,plain,
    ( spl4_3
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f202,plain,
    ( spl4_6
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f647,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f646])).

fof(f646,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK0,sK1)
    | spl4_3
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f644])).

fof(f644,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1)
    | spl4_3
    | ~ spl4_6 ),
    inference(superposition,[],[f97,f548])).

fof(f548,plain,
    ( ! [X2,X3,X1] :
        ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X3))) = X1
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X2,X1) )
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f547,f68])).

fof(f68,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f547,plain,
    ( ! [X2,X3,X1] :
        ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X3)))
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X2,X1) )
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f544,f253])).

fof(f253,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f243,f251])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k5_xboole_0(X0,X0),k1_xboole_0),X0)
        | k1_xboole_0 = k5_xboole_0(X0,X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f219,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f219,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(sK2(k5_xboole_0(X6,X6),k1_xboole_0),X7)
        | k1_xboole_0 = k5_xboole_0(X6,X6) )
    | ~ spl4_6 ),
    inference(resolution,[],[f207,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f84,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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

fof(f207,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0,k1_xboole_0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(superposition,[],[f131,f203])).

fof(f203,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f202])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0)
      | k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f130,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f130,plain,(
    ! [X2] : ~ r2_hidden(X2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f128,f129])).

fof(f129,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f84,f125])).

fof(f125,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f117,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f117,plain,(
    ! [X13] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X13)) = X13 ),
    inference(superposition,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f64,f64])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f128,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f85,f125])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f243,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,X0)
        | r2_hidden(sK2(k5_xboole_0(X0,X0),k1_xboole_0),X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f218,f81])).

fof(f218,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,X5)
        | r2_hidden(sK2(k5_xboole_0(X4,X4),k1_xboole_0),X4)
        | k1_xboole_0 = k5_xboole_0(X4,X4) )
    | ~ spl4_6 ),
    inference(resolution,[],[f207,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,X0))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f85,f46])).

fof(f544,plain,(
    ! [X2,X3,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X3))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_enumset1(X2,X2,X2,X2,X3))))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f183,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) ) ),
    inference(superposition,[],[f71,f46])).

fof(f71,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f45,f65,f44,f65])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f97,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f204,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f191,f202])).

fof(f191,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f188,f125])).

fof(f188,plain,(
    ! [X2] : k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2 ),
    inference(forward_demodulation,[],[f185,f117])).

fof(f185,plain,(
    ! [X2] : k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) ),
    inference(superposition,[],[f71,f117])).

fof(f98,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f94,f87,f96])).

fof(f87,plain,
    ( spl4_1
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f94,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_1 ),
    inference(forward_demodulation,[],[f88,f69])).

fof(f88,plain,
    ( sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f93,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f89,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f67,f87])).

fof(f67,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f37,f65,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:36:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (22386)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (22407)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (22401)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (22384)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.53  % (22404)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (22396)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.53  % (22387)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.53  % (22381)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.53  % (22404)Refutation not found, incomplete strategy% (22404)------------------------------
% 1.26/0.53  % (22404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (22404)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (22404)Memory used [KB]: 10746
% 1.26/0.53  % (22404)Time elapsed: 0.068 s
% 1.26/0.53  % (22404)------------------------------
% 1.26/0.53  % (22404)------------------------------
% 1.26/0.53  % (22381)Refutation not found, incomplete strategy% (22381)------------------------------
% 1.26/0.53  % (22381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (22381)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (22381)Memory used [KB]: 1663
% 1.26/0.53  % (22381)Time elapsed: 0.114 s
% 1.26/0.53  % (22381)------------------------------
% 1.26/0.53  % (22381)------------------------------
% 1.26/0.54  % (22391)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.54  % (22385)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.54  % (22391)Refutation not found, incomplete strategy% (22391)------------------------------
% 1.26/0.54  % (22391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (22391)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (22391)Memory used [KB]: 10618
% 1.26/0.54  % (22391)Time elapsed: 0.118 s
% 1.26/0.54  % (22391)------------------------------
% 1.26/0.54  % (22391)------------------------------
% 1.26/0.54  % (22395)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.54  % (22383)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.54  % (22403)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.54  % (22383)Refutation not found, incomplete strategy% (22383)------------------------------
% 1.26/0.54  % (22383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (22383)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (22383)Memory used [KB]: 10618
% 1.26/0.54  % (22383)Time elapsed: 0.124 s
% 1.26/0.54  % (22383)------------------------------
% 1.26/0.54  % (22383)------------------------------
% 1.42/0.54  % (22394)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.54  % (22412)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.54  % (22405)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.55  % (22408)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (22388)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.55  % (22411)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (22382)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.55  % (22401)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f649,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f89,f93,f98,f204,f648])).
% 1.42/0.55  fof(f648,plain,(
% 1.42/0.55    ~spl4_2 | spl4_3 | ~spl4_6),
% 1.42/0.55    inference(avatar_split_clause,[],[f647,f202,f96,f91])).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    spl4_2 <=> r2_hidden(sK0,sK1)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.42/0.55  fof(f96,plain,(
% 1.42/0.55    spl4_3 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.42/0.55  fof(f202,plain,(
% 1.42/0.55    spl4_6 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.42/0.55  fof(f647,plain,(
% 1.42/0.55    ~r2_hidden(sK0,sK1) | (spl4_3 | ~spl4_6)),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f646])).
% 1.42/0.55  fof(f646,plain,(
% 1.42/0.55    sK1 != sK1 | ~r2_hidden(sK0,sK1) | (spl4_3 | ~spl4_6)),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f644])).
% 1.42/0.55  fof(f644,plain,(
% 1.42/0.55    sK1 != sK1 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1) | (spl4_3 | ~spl4_6)),
% 1.42/0.55    inference(superposition,[],[f97,f548])).
% 1.42/0.55  fof(f548,plain,(
% 1.42/0.55    ( ! [X2,X3,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X3))) = X1 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) ) | ~spl4_6),
% 1.42/0.55    inference(forward_demodulation,[],[f547,f68])).
% 1.42/0.55  fof(f68,plain,(
% 1.42/0.55    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.42/0.55    inference(definition_unfolding,[],[f38,f65])).
% 1.42/0.55  fof(f65,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f42,f64])).
% 1.42/0.55  fof(f64,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f43,f63])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f52,f62])).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f14,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.42/0.55  fof(f52,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f13])).
% 1.42/0.55  fof(f13,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.42/0.55  fof(f547,plain,(
% 1.42/0.55    ( ! [X2,X3,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X3))) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) ) | ~spl4_6),
% 1.42/0.55    inference(forward_demodulation,[],[f544,f253])).
% 1.42/0.55  fof(f253,plain,(
% 1.42/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl4_6),
% 1.42/0.55    inference(subsumption_resolution,[],[f243,f251])).
% 1.42/0.55  fof(f251,plain,(
% 1.42/0.55    ( ! [X0] : (~r2_hidden(sK2(k5_xboole_0(X0,X0),k1_xboole_0),X0) | k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl4_6),
% 1.42/0.55    inference(resolution,[],[f219,f81])).
% 1.42/0.55  fof(f81,plain,(
% 1.42/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.55    inference(equality_resolution,[],[f50])).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.55    inference(flattening,[],[f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.55  fof(f219,plain,(
% 1.42/0.55    ( ! [X6,X7] : (~r1_tarski(X6,X7) | ~r2_hidden(sK2(k5_xboole_0(X6,X6),k1_xboole_0),X7) | k1_xboole_0 = k5_xboole_0(X6,X6)) ) | ~spl4_6),
% 1.42/0.55    inference(resolution,[],[f207,f100])).
% 1.42/0.55  fof(f100,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,X0)) | ~r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(superposition,[],[f84,f46])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.42/0.55  fof(f84,plain,(
% 1.42/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.42/0.55    inference(equality_resolution,[],[f76])).
% 1.42/0.55  fof(f76,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.42/0.55    inference(definition_unfolding,[],[f54,f44])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.42/0.55  fof(f54,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.42/0.55    inference(cnf_transformation,[],[f33])).
% 1.42/0.55  fof(f33,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(rectify,[],[f30])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(flattening,[],[f29])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(nnf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.42/0.55  fof(f207,plain,(
% 1.42/0.55    ( ! [X0] : (r2_hidden(sK2(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 1.42/0.55    inference(superposition,[],[f131,f203])).
% 1.42/0.55  fof(f203,plain,(
% 1.42/0.55    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_6),
% 1.42/0.55    inference(avatar_component_clause,[],[f202])).
% 1.42/0.55  fof(f131,plain,(
% 1.42/0.55    ( ! [X0] : (r2_hidden(sK2(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0) | k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0) )),
% 1.42/0.55    inference(resolution,[],[f130,f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.42/0.55    inference(nnf_transformation,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.42/0.55    inference(ennf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.42/0.55  fof(f130,plain,(
% 1.42/0.55    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f128,f129])).
% 1.42/0.55  fof(f129,plain,(
% 1.42/0.55    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X4,X3)) )),
% 1.42/0.55    inference(superposition,[],[f84,f125])).
% 1.42/0.55  fof(f125,plain,(
% 1.42/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.42/0.55    inference(superposition,[],[f117,f70])).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.42/0.55    inference(definition_unfolding,[],[f41,f65])).
% 1.42/0.55  fof(f41,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.42/0.55  fof(f117,plain,(
% 1.42/0.55    ( ! [X13] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X13)) = X13) )),
% 1.42/0.55    inference(superposition,[],[f68,f69])).
% 1.42/0.55  fof(f69,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f40,f64,f64])).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.42/0.55  fof(f128,plain,(
% 1.42/0.55    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | r2_hidden(X2,k1_xboole_0)) )),
% 1.42/0.55    inference(superposition,[],[f85,f125])).
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f77])).
% 1.42/0.55  fof(f77,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.42/0.55    inference(definition_unfolding,[],[f53,f44])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.42/0.55    inference(cnf_transformation,[],[f33])).
% 1.42/0.55  fof(f243,plain,(
% 1.42/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | r2_hidden(sK2(k5_xboole_0(X0,X0),k1_xboole_0),X0)) ) | ~spl4_6),
% 1.42/0.55    inference(resolution,[],[f218,f81])).
% 1.42/0.55  fof(f218,plain,(
% 1.42/0.55    ( ! [X4,X5] : (~r1_tarski(X4,X5) | r2_hidden(sK2(k5_xboole_0(X4,X4),k1_xboole_0),X4) | k1_xboole_0 = k5_xboole_0(X4,X4)) ) | ~spl4_6),
% 1.42/0.55    inference(resolution,[],[f207,f101])).
% 1.42/0.55  fof(f101,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,X0)) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(superposition,[],[f85,f46])).
% 1.42/0.55  fof(f544,plain,(
% 1.42/0.55    ( ! [X2,X3,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X3))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_enumset1(X2,X2,X2,X2,X3)))) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) )),
% 1.42/0.55    inference(resolution,[],[f183,f78])).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f61,f64])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f35])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.42/0.55    inference(flattening,[],[f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.42/0.55    inference(nnf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.42/0.55  fof(f183,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))) )),
% 1.42/0.55    inference(superposition,[],[f71,f46])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f45,f65,f44,f65])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.42/0.55  fof(f97,plain,(
% 1.42/0.55    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_3),
% 1.42/0.55    inference(avatar_component_clause,[],[f96])).
% 1.42/0.55  fof(f204,plain,(
% 1.42/0.55    spl4_6),
% 1.42/0.55    inference(avatar_split_clause,[],[f191,f202])).
% 1.42/0.55  fof(f191,plain,(
% 1.42/0.55    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.42/0.55    inference(superposition,[],[f188,f125])).
% 1.42/0.55  fof(f188,plain,(
% 1.42/0.55    ( ! [X2] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2) )),
% 1.42/0.55    inference(forward_demodulation,[],[f185,f117])).
% 1.42/0.55  fof(f185,plain,(
% 1.42/0.55    ( ! [X2] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2))) )),
% 1.42/0.55    inference(superposition,[],[f71,f117])).
% 1.42/0.55  fof(f98,plain,(
% 1.42/0.55    ~spl4_3 | spl4_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f94,f87,f96])).
% 1.42/0.55  fof(f87,plain,(
% 1.42/0.55    spl4_1 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.42/0.55  fof(f94,plain,(
% 1.42/0.55    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_1),
% 1.42/0.55    inference(forward_demodulation,[],[f88,f69])).
% 1.42/0.55  fof(f88,plain,(
% 1.42/0.55    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_1),
% 1.42/0.55    inference(avatar_component_clause,[],[f87])).
% 1.42/0.55  fof(f93,plain,(
% 1.42/0.55    spl4_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f36,f91])).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    r2_hidden(sK0,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.42/0.55    inference(ennf_transformation,[],[f18])).
% 1.42/0.55  fof(f18,negated_conjecture,(
% 1.42/0.55    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.42/0.55    inference(negated_conjecture,[],[f17])).
% 1.42/0.55  fof(f17,conjecture,(
% 1.42/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.42/0.55  fof(f89,plain,(
% 1.42/0.55    ~spl4_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f67,f87])).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.42/0.55    inference(definition_unfolding,[],[f37,f65,f66])).
% 1.42/0.55  fof(f66,plain,(
% 1.42/0.55    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f39,f64])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f11])).
% 1.42/0.55  fof(f11,axiom,(
% 1.42/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f23])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (22401)------------------------------
% 1.42/0.55  % (22401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (22401)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (22401)Memory used [KB]: 11129
% 1.42/0.55  % (22401)Time elapsed: 0.121 s
% 1.42/0.55  % (22401)------------------------------
% 1.42/0.55  % (22401)------------------------------
% 1.42/0.55  % (22379)Success in time 0.186 s
%------------------------------------------------------------------------------
