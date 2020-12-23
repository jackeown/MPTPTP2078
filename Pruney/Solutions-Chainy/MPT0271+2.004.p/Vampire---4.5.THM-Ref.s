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
% DateTime   : Thu Dec  3 12:41:05 EST 2020

% Result     : Theorem 5.04s
% Output     : Refutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 110 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 ( 357 expanded)
%              Number of equality atoms :  142 ( 165 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1688,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f1606,f1614,f1629,f1687])).

fof(f1687,plain,
    ( spl4_2
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f1686])).

fof(f1686,plain,
    ( $false
    | spl4_2
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1677,f96])).

fof(f96,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1677,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_12 ),
    inference(resolution,[],[f1633,f129])).

fof(f129,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f104,f66])).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f104,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f84,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1633,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl4_12 ),
    inference(superposition,[],[f86,f1193])).

fof(f1193,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f1191])).

fof(f1191,plain,
    ( spl4_12
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1629,plain,
    ( spl4_12
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f1628,f90,f1191])).

fof(f90,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1628,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1621,f69])).

fof(f69,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1621,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_1 ),
    inference(superposition,[],[f64,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1614,plain,
    ( ~ spl4_2
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1610,f1602,f94])).

fof(f1602,plain,
    ( spl4_13
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1610,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_13 ),
    inference(resolution,[],[f1604,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1604,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f1602])).

fof(f1606,plain,
    ( ~ spl4_13
    | spl4_1 ),
    inference(avatar_split_clause,[],[f1595,f90,f1602])).

fof(f1595,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f1594])).

fof(f1594,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(superposition,[],[f92,f676])).

fof(f676,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f674,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f674,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f65,f672])).

fof(f672,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f172,f217])).

fof(f217,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f149,f63])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f149,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f132,f100])).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f63,f68])).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f132,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f62,f70])).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f172,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f161,f63])).

fof(f161,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f74,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f92,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f98,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f44,f94,f90])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f97,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f45,f94,f90])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:03:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (24782)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (24790)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (24779)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.59  % (24780)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (24784)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.59  % (24793)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.60  % (24806)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.60  % (24789)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.60  % (24791)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.60  % (24802)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.60  % (24796)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.60  % (24783)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  % (24796)Refutation not found, incomplete strategy% (24796)------------------------------
% 0.21/0.60  % (24796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (24796)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (24796)Memory used [KB]: 10618
% 0.21/0.60  % (24796)Time elapsed: 0.168 s
% 0.21/0.60  % (24796)------------------------------
% 0.21/0.60  % (24796)------------------------------
% 0.21/0.60  % (24794)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.60  % (24797)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.60  % (24798)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.60  % (24804)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.60  % (24799)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.61  % (24794)Refutation not found, incomplete strategy% (24794)------------------------------
% 0.21/0.61  % (24794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (24794)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (24794)Memory used [KB]: 6140
% 0.21/0.61  % (24794)Time elapsed: 0.004 s
% 0.21/0.61  % (24794)------------------------------
% 0.21/0.61  % (24794)------------------------------
% 0.21/0.61  % (24792)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.61  % (24781)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.61  % (24786)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.61  % (24807)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.61  % (24808)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.61  % (24800)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.61  % (24785)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.61  % (24803)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.96/0.62  % (24805)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.96/0.62  % (24788)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.96/0.62  % (24801)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.96/0.63  % (24795)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.96/0.63  % (24787)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.55/0.75  % (24833)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.98/0.77  % (24834)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.98/0.84  % (24784)Time limit reached!
% 2.98/0.84  % (24784)------------------------------
% 2.98/0.84  % (24784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.84  % (24784)Termination reason: Time limit
% 2.98/0.84  
% 2.98/0.84  % (24784)Memory used [KB]: 8955
% 2.98/0.84  % (24784)Time elapsed: 0.407 s
% 2.98/0.84  % (24784)------------------------------
% 2.98/0.84  % (24784)------------------------------
% 4.30/0.95  % (24779)Time limit reached!
% 4.30/0.95  % (24779)------------------------------
% 4.30/0.95  % (24779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.95  % (24779)Termination reason: Time limit
% 4.30/0.95  % (24779)Termination phase: Saturation
% 4.30/0.95  
% 4.30/0.95  % (24779)Memory used [KB]: 2558
% 4.30/0.95  % (24779)Time elapsed: 0.500 s
% 4.30/0.95  % (24779)------------------------------
% 4.30/0.95  % (24779)------------------------------
% 4.30/0.96  % (24791)Time limit reached!
% 4.30/0.96  % (24791)------------------------------
% 4.30/0.96  % (24791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.96  % (24791)Termination reason: Time limit
% 4.30/0.96  % (24791)Termination phase: Saturation
% 4.30/0.96  
% 4.30/0.96  % (24791)Memory used [KB]: 11001
% 4.30/0.96  % (24791)Time elapsed: 0.500 s
% 4.30/0.96  % (24791)------------------------------
% 4.30/0.96  % (24791)------------------------------
% 4.30/0.96  % (24789)Time limit reached!
% 4.30/0.96  % (24789)------------------------------
% 4.30/0.96  % (24789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.96  % (24789)Termination reason: Time limit
% 4.30/0.96  
% 4.30/0.96  % (24789)Memory used [KB]: 14456
% 4.30/0.96  % (24789)Time elapsed: 0.530 s
% 4.30/0.96  % (24789)------------------------------
% 4.30/0.96  % (24789)------------------------------
% 4.30/0.97  % (24950)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.30/0.99  % (24780)Time limit reached!
% 4.30/0.99  % (24780)------------------------------
% 4.30/0.99  % (24780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.99  % (24780)Termination reason: Time limit
% 4.30/0.99  
% 4.30/0.99  % (24780)Memory used [KB]: 9338
% 4.30/0.99  % (24780)Time elapsed: 0.515 s
% 4.30/0.99  % (24780)------------------------------
% 4.30/0.99  % (24780)------------------------------
% 4.78/1.04  % (24807)Time limit reached!
% 4.78/1.04  % (24807)------------------------------
% 4.78/1.04  % (24807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.78/1.06  % (24807)Termination reason: Time limit
% 4.78/1.06  
% 4.78/1.06  % (24807)Memory used [KB]: 8699
% 4.78/1.06  % (24807)Time elapsed: 0.615 s
% 4.78/1.06  % (24807)------------------------------
% 4.78/1.06  % (24807)------------------------------
% 4.78/1.06  % (24989)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.04/1.06  % (24795)Time limit reached!
% 5.04/1.06  % (24795)------------------------------
% 5.04/1.06  % (24795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.06  % (24795)Termination reason: Time limit
% 5.04/1.06  % (24795)Termination phase: Saturation
% 5.04/1.06  
% 5.04/1.06  % (24795)Memory used [KB]: 15863
% 5.04/1.06  % (24795)Time elapsed: 0.600 s
% 5.04/1.06  % (24795)------------------------------
% 5.04/1.06  % (24795)------------------------------
% 5.04/1.07  % (24984)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.04/1.08  % (24950)Refutation found. Thanks to Tanya!
% 5.04/1.08  % SZS status Theorem for theBenchmark
% 5.04/1.08  % SZS output start Proof for theBenchmark
% 5.04/1.08  fof(f1688,plain,(
% 5.04/1.08    $false),
% 5.04/1.08    inference(avatar_sat_refutation,[],[f97,f98,f1606,f1614,f1629,f1687])).
% 5.04/1.08  fof(f1687,plain,(
% 5.04/1.08    spl4_2 | ~spl4_12),
% 5.04/1.08    inference(avatar_contradiction_clause,[],[f1686])).
% 5.04/1.08  fof(f1686,plain,(
% 5.04/1.08    $false | (spl4_2 | ~spl4_12)),
% 5.04/1.08    inference(subsumption_resolution,[],[f1677,f96])).
% 5.04/1.08  fof(f96,plain,(
% 5.04/1.08    ~r2_hidden(sK0,sK1) | spl4_2),
% 5.04/1.08    inference(avatar_component_clause,[],[f94])).
% 5.04/1.08  fof(f94,plain,(
% 5.04/1.08    spl4_2 <=> r2_hidden(sK0,sK1)),
% 5.04/1.08    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 5.04/1.08  fof(f1677,plain,(
% 5.04/1.08    r2_hidden(sK0,sK1) | ~spl4_12),
% 5.04/1.08    inference(resolution,[],[f1633,f129])).
% 5.04/1.08  fof(f129,plain,(
% 5.04/1.08    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 5.04/1.08    inference(superposition,[],[f104,f66])).
% 5.04/1.08  fof(f66,plain,(
% 5.04/1.08    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 5.04/1.08    inference(cnf_transformation,[],[f14])).
% 5.04/1.08  fof(f14,axiom,(
% 5.04/1.08    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 5.04/1.08  fof(f104,plain,(
% 5.04/1.08    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 5.04/1.08    inference(superposition,[],[f84,f72])).
% 5.04/1.08  fof(f72,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 5.04/1.08    inference(cnf_transformation,[],[f15])).
% 5.04/1.08  fof(f15,axiom,(
% 5.04/1.08    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.04/1.08  fof(f84,plain,(
% 5.04/1.08    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 5.04/1.08    inference(equality_resolution,[],[f83])).
% 5.04/1.08  fof(f83,plain,(
% 5.04/1.08    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 5.04/1.08    inference(equality_resolution,[],[f47])).
% 5.04/1.08  fof(f47,plain,(
% 5.04/1.08    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 5.04/1.08    inference(cnf_transformation,[],[f37])).
% 5.04/1.08  fof(f37,plain,(
% 5.04/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.04/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 5.04/1.08  fof(f36,plain,(
% 5.04/1.08    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 5.04/1.08    introduced(choice_axiom,[])).
% 5.04/1.08  fof(f35,plain,(
% 5.04/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.04/1.08    inference(rectify,[],[f34])).
% 5.04/1.08  fof(f34,plain,(
% 5.04/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.04/1.08    inference(flattening,[],[f33])).
% 5.04/1.08  fof(f33,plain,(
% 5.04/1.08    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.04/1.08    inference(nnf_transformation,[],[f28])).
% 5.04/1.08  fof(f28,plain,(
% 5.04/1.08    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 5.04/1.08    inference(ennf_transformation,[],[f13])).
% 5.04/1.08  fof(f13,axiom,(
% 5.04/1.08    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 5.04/1.08  fof(f1633,plain,(
% 5.04/1.08    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,sK1)) ) | ~spl4_12),
% 5.04/1.08    inference(superposition,[],[f86,f1193])).
% 5.04/1.08  fof(f1193,plain,(
% 5.04/1.08    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_12),
% 5.04/1.08    inference(avatar_component_clause,[],[f1191])).
% 5.04/1.08  fof(f1191,plain,(
% 5.04/1.08    spl4_12 <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 5.04/1.08    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 5.04/1.08  fof(f86,plain,(
% 5.04/1.08    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 5.04/1.08    inference(equality_resolution,[],[f56])).
% 5.04/1.08  fof(f56,plain,(
% 5.04/1.08    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 5.04/1.08    inference(cnf_transformation,[],[f42])).
% 5.04/1.08  fof(f42,plain,(
% 5.04/1.08    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.04/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 5.04/1.08  fof(f41,plain,(
% 5.04/1.08    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 5.04/1.08    introduced(choice_axiom,[])).
% 5.04/1.08  fof(f40,plain,(
% 5.04/1.08    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.04/1.08    inference(rectify,[],[f39])).
% 5.04/1.08  fof(f39,plain,(
% 5.04/1.08    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.04/1.08    inference(flattening,[],[f38])).
% 5.04/1.08  fof(f38,plain,(
% 5.04/1.08    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.04/1.08    inference(nnf_transformation,[],[f2])).
% 5.04/1.08  fof(f2,axiom,(
% 5.04/1.08    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 5.04/1.08  fof(f1629,plain,(
% 5.04/1.08    spl4_12 | ~spl4_1),
% 5.04/1.08    inference(avatar_split_clause,[],[f1628,f90,f1191])).
% 5.04/1.08  fof(f90,plain,(
% 5.04/1.08    spl4_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.04/1.08    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 5.04/1.08  fof(f1628,plain,(
% 5.04/1.08    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_1),
% 5.04/1.08    inference(forward_demodulation,[],[f1621,f69])).
% 5.04/1.08  fof(f69,plain,(
% 5.04/1.08    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.04/1.08    inference(cnf_transformation,[],[f6])).
% 5.04/1.08  fof(f6,axiom,(
% 5.04/1.08    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 5.04/1.08  fof(f1621,plain,(
% 5.04/1.08    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl4_1),
% 5.04/1.08    inference(superposition,[],[f64,f91])).
% 5.04/1.08  fof(f91,plain,(
% 5.04/1.08    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 5.04/1.08    inference(avatar_component_clause,[],[f90])).
% 5.04/1.08  fof(f64,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.04/1.08    inference(cnf_transformation,[],[f7])).
% 5.04/1.08  fof(f7,axiom,(
% 5.04/1.08    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.04/1.08  fof(f1614,plain,(
% 5.04/1.08    ~spl4_2 | spl4_13),
% 5.04/1.08    inference(avatar_split_clause,[],[f1610,f1602,f94])).
% 5.04/1.08  fof(f1602,plain,(
% 5.04/1.08    spl4_13 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 5.04/1.08    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 5.04/1.08  fof(f1610,plain,(
% 5.04/1.08    ~r2_hidden(sK0,sK1) | spl4_13),
% 5.04/1.08    inference(resolution,[],[f1604,f61])).
% 5.04/1.08  fof(f61,plain,(
% 5.04/1.08    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 5.04/1.08    inference(cnf_transformation,[],[f43])).
% 5.04/1.08  fof(f43,plain,(
% 5.04/1.08    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 5.04/1.08    inference(nnf_transformation,[],[f21])).
% 5.04/1.08  fof(f21,axiom,(
% 5.04/1.08    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 5.04/1.08  fof(f1604,plain,(
% 5.04/1.08    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_13),
% 5.04/1.08    inference(avatar_component_clause,[],[f1602])).
% 5.04/1.08  fof(f1606,plain,(
% 5.04/1.08    ~spl4_13 | spl4_1),
% 5.04/1.08    inference(avatar_split_clause,[],[f1595,f90,f1602])).
% 5.04/1.08  fof(f1595,plain,(
% 5.04/1.08    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 5.04/1.08    inference(trivial_inequality_removal,[],[f1594])).
% 5.04/1.08  fof(f1594,plain,(
% 5.04/1.08    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 5.04/1.08    inference(superposition,[],[f92,f676])).
% 5.04/1.08  fof(f676,plain,(
% 5.04/1.08    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 5.04/1.08    inference(forward_demodulation,[],[f674,f70])).
% 5.04/1.08  fof(f70,plain,(
% 5.04/1.08    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.04/1.08    inference(cnf_transformation,[],[f10])).
% 5.04/1.08  fof(f10,axiom,(
% 5.04/1.08    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.04/1.08  fof(f674,plain,(
% 5.04/1.08    ( ! [X2,X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 5.04/1.08    inference(superposition,[],[f65,f672])).
% 5.04/1.08  fof(f672,plain,(
% 5.04/1.08    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) )),
% 5.04/1.08    inference(forward_demodulation,[],[f172,f217])).
% 5.04/1.08  fof(f217,plain,(
% 5.04/1.08    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 5.04/1.08    inference(superposition,[],[f149,f63])).
% 5.04/1.08  fof(f63,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.04/1.08    inference(cnf_transformation,[],[f1])).
% 5.04/1.08  fof(f1,axiom,(
% 5.04/1.08    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.04/1.08  fof(f149,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.04/1.08    inference(forward_demodulation,[],[f132,f100])).
% 5.04/1.08  fof(f100,plain,(
% 5.04/1.08    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.04/1.08    inference(superposition,[],[f63,f68])).
% 5.04/1.08  fof(f68,plain,(
% 5.04/1.08    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.04/1.08    inference(cnf_transformation,[],[f8])).
% 5.04/1.08  fof(f8,axiom,(
% 5.04/1.08    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 5.04/1.08  fof(f132,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.04/1.08    inference(superposition,[],[f62,f70])).
% 5.04/1.08  fof(f62,plain,(
% 5.04/1.08    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.04/1.08    inference(cnf_transformation,[],[f9])).
% 5.04/1.08  fof(f9,axiom,(
% 5.04/1.08    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.04/1.08  fof(f172,plain,(
% 5.04/1.08    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) | ~r1_tarski(X1,X2)) )),
% 5.04/1.08    inference(forward_demodulation,[],[f161,f63])).
% 5.04/1.08  fof(f161,plain,(
% 5.04/1.08    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2) | ~r1_tarski(X1,X2)) )),
% 5.04/1.08    inference(superposition,[],[f74,f73])).
% 5.04/1.08  fof(f73,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 5.04/1.08    inference(cnf_transformation,[],[f29])).
% 5.04/1.08  fof(f29,plain,(
% 5.04/1.08    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.04/1.08    inference(ennf_transformation,[],[f5])).
% 5.04/1.08  fof(f5,axiom,(
% 5.04/1.08    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.04/1.08  fof(f74,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 5.04/1.08    inference(cnf_transformation,[],[f11])).
% 5.04/1.08  fof(f11,axiom,(
% 5.04/1.08    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 5.04/1.08  fof(f65,plain,(
% 5.04/1.08    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.04/1.08    inference(cnf_transformation,[],[f4])).
% 5.04/1.08  fof(f4,axiom,(
% 5.04/1.08    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.04/1.08  fof(f92,plain,(
% 5.04/1.08    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 5.04/1.08    inference(avatar_component_clause,[],[f90])).
% 5.04/1.08  fof(f98,plain,(
% 5.04/1.08    spl4_1 | spl4_2),
% 5.04/1.08    inference(avatar_split_clause,[],[f44,f94,f90])).
% 5.04/1.08  fof(f44,plain,(
% 5.04/1.08    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.04/1.08    inference(cnf_transformation,[],[f32])).
% 5.04/1.08  fof(f32,plain,(
% 5.04/1.08    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 5.04/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 5.04/1.08  fof(f31,plain,(
% 5.04/1.08    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 5.04/1.08    introduced(choice_axiom,[])).
% 5.04/1.08  fof(f30,plain,(
% 5.04/1.08    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 5.04/1.08    inference(nnf_transformation,[],[f27])).
% 5.04/1.08  fof(f27,plain,(
% 5.04/1.08    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 5.04/1.08    inference(ennf_transformation,[],[f25])).
% 5.04/1.08  fof(f25,negated_conjecture,(
% 5.04/1.08    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.04/1.08    inference(negated_conjecture,[],[f24])).
% 5.04/1.08  fof(f24,conjecture,(
% 5.04/1.08    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.04/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 5.04/1.08  fof(f97,plain,(
% 5.04/1.08    ~spl4_1 | ~spl4_2),
% 5.04/1.08    inference(avatar_split_clause,[],[f45,f94,f90])).
% 5.04/1.08  fof(f45,plain,(
% 5.04/1.08    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.04/1.08    inference(cnf_transformation,[],[f32])).
% 5.04/1.08  % SZS output end Proof for theBenchmark
% 5.04/1.08  % (24950)------------------------------
% 5.04/1.08  % (24950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.08  % (24950)Termination reason: Refutation
% 5.04/1.08  
% 5.04/1.08  % (24950)Memory used [KB]: 7675
% 5.04/1.08  % (24950)Time elapsed: 0.181 s
% 5.04/1.08  % (24950)------------------------------
% 5.04/1.08  % (24950)------------------------------
% 5.04/1.08  % (24778)Success in time 0.71 s
%------------------------------------------------------------------------------
