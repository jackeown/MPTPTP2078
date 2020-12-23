%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:18 EST 2020

% Result     : Theorem 13.31s
% Output     : Refutation 13.31s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 625 expanded)
%              Number of leaves         :   33 ( 199 expanded)
%              Depth                    :   15
%              Number of atoms          :  593 (2422 expanded)
%              Number of equality atoms :  239 (1501 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f302,f378,f403,f472,f476,f728,f8736,f11029,f11039,f11049,f11381,f11480,f11483,f11537,f11790,f11980,f13418])).

fof(f13418,plain,
    ( spl5_2
    | spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f13417])).

fof(f13417,plain,
    ( $false
    | spl5_2
    | spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f13396,f123])).

fof(f123,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f84,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f13396,plain,
    ( ~ r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_2
    | spl5_3
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f12033,f13356])).

fof(f13356,plain,
    ( ! [X0] : k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,sK1),sK2))
    | spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f11632,f11894,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) ) ),
    inference(definition_unfolding,[],[f66,f91,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f90])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f11894,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK1,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK1),sK2))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f123,f401,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f401,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl5_6
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f11632,plain,
    ( ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,X1),sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f127,f301,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f301,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f127,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f82,f89])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12033,plain,
    ( ~ r2_hidden(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f11996,f235])).

fof(f235,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k3_xboole_0(X7,X6)) = k3_xboole_0(X6,k5_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f221,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f221,plain,(
    ! [X6,X7] : k3_xboole_0(k5_xboole_0(X6,X7),X6) = k5_xboole_0(X6,k3_xboole_0(X7,X6)) ),
    inference(superposition,[],[f65,f129])).

fof(f129,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f116,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f11996,plain,
    ( ~ r2_hidden(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f341,f341,f341,f128])).

fof(f128,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f81,f89])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f341,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl5_3
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f11980,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f11527,f295,f339])).

fof(f295,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f11527,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f296,f54])).

fof(f296,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f295])).

fof(f11790,plain,
    ( spl5_2
    | spl5_16
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f11789])).

fof(f11789,plain,
    ( $false
    | spl5_2
    | spl5_16
    | spl5_21 ),
    inference(subsumption_resolution,[],[f11774,f125])).

fof(f125,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f83,f89])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11774,plain,
    ( ~ r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))
    | spl5_2
    | spl5_16
    | spl5_21 ),
    inference(backward_demodulation,[],[f11606,f11711])).

fof(f11711,plain,
    ( ! [X0,X1] : k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f11630,f118])).

fof(f118,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f91,f90])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11630,plain,
    ( ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f123,f301,f78])).

fof(f11606,plain,
    ( ~ r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k1_xboole_0))
    | spl5_16
    | spl5_21 ),
    inference(forward_demodulation,[],[f11567,f235])).

fof(f11567,plain,
    ( ~ r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0))
    | spl5_16
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f11536,f11536,f11344,f128])).

fof(f11344,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f11343])).

fof(f11343,plain,
    ( spl5_16
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f11536,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f11534])).

fof(f11534,plain,
    ( spl5_21
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f11537,plain,
    ( ~ spl5_21
    | spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f11528,f375,f295,f11534])).

fof(f375,plain,
    ( spl5_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f11528,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f11527,f376])).

fof(f376,plain,
    ( sK0 = sK1
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f375])).

fof(f11483,plain,
    ( sK0 != sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f11480,plain,(
    ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f11479])).

fof(f11479,plain,
    ( $false
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f11478,f127])).

fof(f11478,plain,
    ( ! [X39,X38] : ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,X38,X39))
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f11413,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f11413,plain,
    ( ! [X39,X38] : ~ r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X38,X39),k1_xboole_0))
    | ~ spl5_16 ),
    inference(superposition,[],[f182,f11345])).

fof(f11345,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f11343])).

fof(f182,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X3,X4))) ),
    inference(unit_resulting_resolution,[],[f127,f127,f77])).

fof(f11381,plain,
    ( spl5_16
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f11050,f11041,f11343])).

fof(f11041,plain,
    ( spl5_13
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f11050,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f11043,f135])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f133,f129])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f116,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f62,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f11043,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f11041])).

fof(f11049,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f11039,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f8863,f400,f299,f11036])).

fof(f11036,plain,
    ( spl5_12
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f8863,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f300,f401,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f90,f90])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f300,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f299])).

fof(f11029,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f8775,f299,f11026])).

fof(f11026,plain,
    ( spl5_10
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f8775,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f300,f118])).

fof(f8736,plain,
    ( ~ spl5_3
    | spl5_6
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f8735])).

fof(f8735,plain,
    ( $false
    | ~ spl5_3
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f8734,f123])).

fof(f8734,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_3
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f8720,f727])).

fof(f727,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl5_8
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f8720,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f478,f679])).

fof(f679,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k3_xboole_0(sK2,X0))
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f402,f417,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f417,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f402,f121])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f70,f56])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f402,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f400])).

fof(f478,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
        | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f78,f340])).

fof(f340,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f339])).

fof(f728,plain,
    ( ~ spl5_8
    | spl5_5 ),
    inference(avatar_split_clause,[],[f385,f375,f725])).

fof(f385,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f377,f377,f377,f128])).

fof(f377,plain,
    ( sK0 != sK1
    | spl5_5 ),
    inference(avatar_component_clause,[],[f375])).

fof(f476,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f473,f295,f339])).

fof(f473,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f297,f54])).

fof(f297,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f295])).

fof(f472,plain,
    ( spl5_1
    | spl5_6
    | spl5_5 ),
    inference(avatar_split_clause,[],[f94,f375,f400,f295])).

fof(f94,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f49,f91,f56,f90])).

fof(f49,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f403,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f93,f400,f299,f295])).

fof(f93,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f50,f91,f56,f90])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f378,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f92,f375,f299,f295])).

fof(f92,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f51,f91,f56,f90])).

fof(f51,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f302,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f95,f299,f295])).

fof(f95,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f48,f91,f56,f90])).

fof(f48,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (19468)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.52  % (19484)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.21/0.52  % (19465)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.21/0.52  % (19485)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.21/0.52  % (19477)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.21/0.53  % (19467)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.21/0.53  % (19469)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.21/0.53  % (19476)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.54  % (19473)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.55  % (19466)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.55  % (19463)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.55  % (19464)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.55  % (19491)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.55  % (19490)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.56  % (19487)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.56  % (19489)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.56  % (19480)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.56  % (19483)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.56  % (19481)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.56  % (19462)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.56  % (19479)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.56  % (19482)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.56  % (19488)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.57  % (19471)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.57  % (19475)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.57  % (19474)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.57  % (19472)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.33/0.57  % (19478)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.57  % (19486)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.58  % (19470)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.59  % (19478)Refutation not found, incomplete strategy% (19478)------------------------------
% 1.33/0.59  % (19478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.59  % (19478)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.59  
% 1.33/0.59  % (19478)Memory used [KB]: 10746
% 1.33/0.59  % (19478)Time elapsed: 0.174 s
% 1.33/0.59  % (19478)------------------------------
% 1.33/0.59  % (19478)------------------------------
% 2.47/0.69  % (19465)Refutation not found, incomplete strategy% (19465)------------------------------
% 2.47/0.69  % (19465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.47/0.69  % (19465)Termination reason: Refutation not found, incomplete strategy
% 2.47/0.69  
% 2.47/0.69  % (19465)Memory used [KB]: 6268
% 2.47/0.69  % (19465)Time elapsed: 0.275 s
% 2.47/0.69  % (19465)------------------------------
% 2.47/0.69  % (19465)------------------------------
% 2.47/0.72  % (19492)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.36/0.83  % (19486)Time limit reached!
% 3.36/0.83  % (19486)------------------------------
% 3.36/0.83  % (19486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.83  % (19464)Time limit reached!
% 3.36/0.83  % (19464)------------------------------
% 3.36/0.83  % (19464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.83  % (19464)Termination reason: Time limit
% 3.36/0.83  
% 3.36/0.83  % (19464)Memory used [KB]: 6524
% 3.36/0.83  % (19464)Time elapsed: 0.412 s
% 3.36/0.83  % (19464)------------------------------
% 3.36/0.83  % (19464)------------------------------
% 3.36/0.83  % (19486)Termination reason: Time limit
% 3.36/0.83  % (19486)Termination phase: Saturation
% 3.36/0.83  
% 3.36/0.83  % (19486)Memory used [KB]: 12792
% 3.36/0.83  % (19486)Time elapsed: 0.400 s
% 3.36/0.83  % (19486)------------------------------
% 3.36/0.83  % (19486)------------------------------
% 3.56/0.84  % (19488)Refutation not found, incomplete strategy% (19488)------------------------------
% 3.56/0.84  % (19488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.84  % (19488)Termination reason: Refutation not found, incomplete strategy
% 3.56/0.84  
% 3.56/0.84  % (19488)Memory used [KB]: 7931
% 3.56/0.84  % (19488)Time elapsed: 0.425 s
% 3.56/0.84  % (19488)------------------------------
% 3.56/0.84  % (19488)------------------------------
% 3.56/0.85  % (19493)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.56/0.92  % (19491)Time limit reached!
% 3.56/0.92  % (19491)------------------------------
% 3.56/0.92  % (19491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.92  % (19491)Termination reason: Time limit
% 3.56/0.92  % (19491)Termination phase: Saturation
% 3.56/0.92  
% 3.56/0.92  % (19491)Memory used [KB]: 2814
% 3.56/0.92  % (19491)Time elapsed: 0.500 s
% 3.56/0.92  % (19491)------------------------------
% 3.56/0.92  % (19491)------------------------------
% 3.56/0.92  % (19468)Time limit reached!
% 3.56/0.92  % (19468)------------------------------
% 3.56/0.92  % (19468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.92  % (19468)Termination reason: Time limit
% 3.56/0.92  % (19468)Termination phase: Saturation
% 3.56/0.92  
% 3.56/0.92  % (19468)Memory used [KB]: 14583
% 3.56/0.92  % (19468)Time elapsed: 0.500 s
% 3.56/0.92  % (19468)------------------------------
% 3.56/0.92  % (19468)------------------------------
% 4.21/0.93  % (19476)Time limit reached!
% 4.21/0.93  % (19476)------------------------------
% 4.21/0.93  % (19476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.93  % (19476)Termination reason: Time limit
% 4.21/0.93  % (19476)Termination phase: Saturation
% 4.21/0.93  
% 4.21/0.93  % (19476)Memory used [KB]: 3709
% 4.21/0.93  % (19476)Time elapsed: 0.500 s
% 4.21/0.93  % (19476)------------------------------
% 4.21/0.93  % (19476)------------------------------
% 4.21/0.94  % (19495)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.21/0.96  % (19496)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.21/0.96  % (19496)Refutation not found, incomplete strategy% (19496)------------------------------
% 4.21/0.96  % (19496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.96  % (19496)Termination reason: Refutation not found, incomplete strategy
% 4.21/0.96  
% 4.21/0.96  % (19496)Memory used [KB]: 10746
% 4.21/0.96  % (19496)Time elapsed: 0.100 s
% 4.21/0.96  % (19496)------------------------------
% 4.21/0.96  % (19496)------------------------------
% 4.21/0.97  % (19494)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.57/1.06  % (19498)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.04/1.06  % (19497)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.52/1.08  % (19499)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.52/1.10  % (19469)Time limit reached!
% 5.52/1.10  % (19469)------------------------------
% 5.52/1.10  % (19469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.52/1.10  % (19469)Termination reason: Time limit
% 5.52/1.10  
% 5.52/1.10  % (19469)Memory used [KB]: 5756
% 5.52/1.10  % (19469)Time elapsed: 0.636 s
% 5.52/1.10  % (19469)------------------------------
% 5.52/1.10  % (19469)------------------------------
% 5.52/1.10  % (19500)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.09/1.22  % (19463)Time limit reached!
% 6.09/1.22  % (19463)------------------------------
% 6.09/1.22  % (19463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.71/1.24  % (19463)Termination reason: Time limit
% 6.71/1.24  
% 6.71/1.24  % (19463)Memory used [KB]: 3837
% 6.71/1.24  % (19463)Time elapsed: 0.801 s
% 6.71/1.24  % (19463)------------------------------
% 6.71/1.24  % (19463)------------------------------
% 7.08/1.28  % (19501)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.75/1.38  % (19502)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 8.13/1.43  % (19474)Time limit reached!
% 8.13/1.43  % (19474)------------------------------
% 8.13/1.43  % (19474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.13/1.43  % (19474)Termination reason: Time limit
% 8.13/1.43  
% 8.13/1.43  % (19474)Memory used [KB]: 12792
% 8.13/1.43  % (19474)Time elapsed: 1.017 s
% 8.13/1.43  % (19474)------------------------------
% 8.13/1.43  % (19474)------------------------------
% 8.13/1.44  % (19489)Time limit reached!
% 8.13/1.44  % (19489)------------------------------
% 8.13/1.44  % (19489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.13/1.44  % (19489)Termination reason: Time limit
% 8.13/1.44  % (19489)Termination phase: Saturation
% 8.13/1.44  
% 8.13/1.44  % (19489)Memory used [KB]: 9850
% 8.13/1.44  % (19489)Time elapsed: 1.0000 s
% 8.13/1.44  % (19489)------------------------------
% 8.13/1.44  % (19489)------------------------------
% 8.90/1.56  % (19498)Time limit reached!
% 8.90/1.56  % (19498)------------------------------
% 8.90/1.56  % (19498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.90/1.56  % (19498)Termination reason: Time limit
% 8.90/1.56  % (19498)Termination phase: Saturation
% 8.90/1.56  
% 8.90/1.56  % (19498)Memory used [KB]: 16375
% 8.90/1.56  % (19498)Time elapsed: 0.615 s
% 8.90/1.56  % (19498)------------------------------
% 8.90/1.56  % (19498)------------------------------
% 8.90/1.57  % (19503)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 8.90/1.57  % (19504)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.16/1.67  % (19462)Time limit reached!
% 10.16/1.67  % (19462)------------------------------
% 10.16/1.67  % (19462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.16/1.67  % (19462)Termination reason: Time limit
% 10.16/1.67  
% 10.16/1.67  % (19462)Memory used [KB]: 10874
% 10.16/1.67  % (19462)Time elapsed: 1.225 s
% 10.16/1.67  % (19462)------------------------------
% 10.16/1.67  % (19462)------------------------------
% 10.16/1.67  % (19494)Time limit reached!
% 10.16/1.67  % (19494)------------------------------
% 10.16/1.67  % (19494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.16/1.67  % (19494)Termination reason: Time limit
% 10.16/1.67  
% 10.16/1.67  % (19494)Memory used [KB]: 11385
% 10.16/1.67  % (19494)Time elapsed: 0.809 s
% 10.16/1.67  % (19494)------------------------------
% 10.16/1.67  % (19494)------------------------------
% 10.33/1.69  % (19505)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 10.33/1.72  % (19505)Refutation not found, incomplete strategy% (19505)------------------------------
% 10.33/1.72  % (19505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.33/1.72  % (19505)Termination reason: Refutation not found, incomplete strategy
% 10.33/1.72  
% 10.33/1.72  % (19505)Memory used [KB]: 10746
% 10.33/1.72  % (19505)Time elapsed: 0.114 s
% 10.33/1.72  % (19505)------------------------------
% 10.33/1.72  % (19505)------------------------------
% 10.33/1.72  % (19467)Time limit reached!
% 10.33/1.72  % (19467)------------------------------
% 10.33/1.72  % (19467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.75/1.74  % (19467)Termination reason: Time limit
% 10.75/1.74  % (19467)Termination phase: Saturation
% 10.75/1.74  
% 10.75/1.74  % (19467)Memory used [KB]: 8827
% 10.75/1.74  % (19467)Time elapsed: 1.300 s
% 10.75/1.74  % (19467)------------------------------
% 10.75/1.74  % (19467)------------------------------
% 11.38/1.82  % (19507)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 11.38/1.84  % (19508)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 11.38/1.84  % (19506)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.38/1.86  % (19509)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 12.24/1.95  % (19501)Time limit reached!
% 12.24/1.95  % (19501)------------------------------
% 12.24/1.95  % (19501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.24/1.95  % (19501)Termination reason: Time limit
% 12.24/1.95  % (19501)Termination phase: Saturation
% 12.24/1.95  
% 12.24/1.95  % (19501)Memory used [KB]: 14456
% 12.24/1.95  % (19501)Time elapsed: 0.800 s
% 12.24/1.95  % (19501)------------------------------
% 12.24/1.95  % (19501)------------------------------
% 12.86/2.08  % (19510)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 13.31/2.16  % (19507)Time limit reached!
% 13.31/2.16  % (19507)------------------------------
% 13.31/2.16  % (19507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.31/2.16  % (19507)Termination reason: Time limit
% 13.31/2.16  
% 13.31/2.16  % (19507)Memory used [KB]: 8955
% 13.31/2.16  % (19507)Time elapsed: 0.442 s
% 13.31/2.16  % (19507)------------------------------
% 13.31/2.16  % (19507)------------------------------
% 13.31/2.17  % (19482)Refutation found. Thanks to Tanya!
% 13.31/2.17  % SZS status Theorem for theBenchmark
% 13.31/2.17  % SZS output start Proof for theBenchmark
% 13.31/2.17  fof(f13462,plain,(
% 13.31/2.17    $false),
% 13.31/2.17    inference(avatar_sat_refutation,[],[f302,f378,f403,f472,f476,f728,f8736,f11029,f11039,f11049,f11381,f11480,f11483,f11537,f11790,f11980,f13418])).
% 13.31/2.17  fof(f13418,plain,(
% 13.31/2.17    spl5_2 | spl5_3 | ~spl5_6),
% 13.31/2.17    inference(avatar_contradiction_clause,[],[f13417])).
% 13.31/2.17  fof(f13417,plain,(
% 13.31/2.17    $false | (spl5_2 | spl5_3 | ~spl5_6)),
% 13.31/2.17    inference(subsumption_resolution,[],[f13396,f123])).
% 13.31/2.17  fof(f123,plain,(
% 13.31/2.17    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 13.31/2.17    inference(equality_resolution,[],[f122])).
% 13.31/2.17  fof(f122,plain,(
% 13.31/2.17    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 13.31/2.17    inference(equality_resolution,[],[f112])).
% 13.31/2.17  fof(f112,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 13.31/2.17    inference(definition_unfolding,[],[f84,f89])).
% 13.31/2.17  fof(f89,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 13.31/2.17    inference(definition_unfolding,[],[f63,f80])).
% 13.31/2.17  fof(f80,plain,(
% 13.31/2.17    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f15])).
% 13.31/2.17  fof(f15,axiom,(
% 13.31/2.17    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 13.31/2.17  fof(f63,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f14])).
% 13.31/2.17  fof(f14,axiom,(
% 13.31/2.17    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 13.31/2.17  fof(f84,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 13.31/2.17    inference(cnf_transformation,[],[f47])).
% 13.31/2.17  fof(f47,plain,(
% 13.31/2.17    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.31/2.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 13.31/2.17  fof(f46,plain,(
% 13.31/2.17    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 13.31/2.17    introduced(choice_axiom,[])).
% 13.31/2.17  fof(f45,plain,(
% 13.31/2.17    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.31/2.17    inference(rectify,[],[f44])).
% 13.31/2.17  fof(f44,plain,(
% 13.31/2.17    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.31/2.17    inference(flattening,[],[f43])).
% 13.31/2.17  fof(f43,plain,(
% 13.31/2.17    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.31/2.17    inference(nnf_transformation,[],[f29])).
% 13.31/2.17  fof(f29,plain,(
% 13.31/2.17    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 13.31/2.17    inference(ennf_transformation,[],[f11])).
% 13.31/2.17  fof(f11,axiom,(
% 13.31/2.17    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 13.31/2.17  fof(f13396,plain,(
% 13.31/2.17    ~r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (spl5_2 | spl5_3 | ~spl5_6)),
% 13.31/2.17    inference(backward_demodulation,[],[f12033,f13356])).
% 13.31/2.17  fof(f13356,plain,(
% 13.31/2.17    ( ! [X0] : (k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,sK1),sK2))) ) | (spl5_2 | ~spl5_6)),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f11632,f11894,f99])).
% 13.31/2.17  fof(f99,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)) )),
% 13.31/2.17    inference(definition_unfolding,[],[f66,f91,f90])).
% 13.31/2.17  fof(f90,plain,(
% 13.31/2.17    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 13.31/2.17    inference(definition_unfolding,[],[f55,f89])).
% 13.31/2.17  fof(f55,plain,(
% 13.31/2.17    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f13])).
% 13.31/2.17  fof(f13,axiom,(
% 13.31/2.17    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 13.31/2.17  fof(f91,plain,(
% 13.31/2.17    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 13.31/2.17    inference(definition_unfolding,[],[f53,f90])).
% 13.31/2.17  fof(f53,plain,(
% 13.31/2.17    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f12])).
% 13.31/2.17  fof(f12,axiom,(
% 13.31/2.17    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 13.31/2.17  fof(f66,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f24])).
% 13.31/2.17  fof(f24,plain,(
% 13.31/2.17    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 13.31/2.17    inference(flattening,[],[f23])).
% 13.31/2.17  fof(f23,plain,(
% 13.31/2.17    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 13.31/2.17    inference(ennf_transformation,[],[f17])).
% 13.31/2.17  fof(f17,axiom,(
% 13.31/2.17    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 13.31/2.17  fof(f11894,plain,(
% 13.31/2.17    ( ! [X0,X1] : (~r2_hidden(sK1,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK1),sK2))) ) | ~spl5_6),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f123,f401,f77])).
% 13.31/2.17  fof(f77,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f42])).
% 13.31/2.17  fof(f42,plain,(
% 13.31/2.17    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 13.31/2.17    inference(nnf_transformation,[],[f28])).
% 13.31/2.17  fof(f28,plain,(
% 13.31/2.17    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 13.31/2.17    inference(ennf_transformation,[],[f3])).
% 13.31/2.17  fof(f3,axiom,(
% 13.31/2.17    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 13.31/2.17  fof(f401,plain,(
% 13.31/2.17    r2_hidden(sK1,sK2) | ~spl5_6),
% 13.31/2.17    inference(avatar_component_clause,[],[f400])).
% 13.31/2.17  fof(f400,plain,(
% 13.31/2.17    spl5_6 <=> r2_hidden(sK1,sK2)),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 13.31/2.17  fof(f11632,plain,(
% 13.31/2.17    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,X1),sK2))) ) | spl5_2),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f127,f301,f78])).
% 13.31/2.17  fof(f78,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f42])).
% 13.31/2.17  fof(f301,plain,(
% 13.31/2.17    ~r2_hidden(sK0,sK2) | spl5_2),
% 13.31/2.17    inference(avatar_component_clause,[],[f299])).
% 13.31/2.17  fof(f299,plain,(
% 13.31/2.17    spl5_2 <=> r2_hidden(sK0,sK2)),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 13.31/2.17  fof(f127,plain,(
% 13.31/2.17    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 13.31/2.17    inference(equality_resolution,[],[f126])).
% 13.31/2.17  fof(f126,plain,(
% 13.31/2.17    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 13.31/2.17    inference(equality_resolution,[],[f114])).
% 13.31/2.17  fof(f114,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 13.31/2.17    inference(definition_unfolding,[],[f82,f89])).
% 13.31/2.17  fof(f82,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 13.31/2.17    inference(cnf_transformation,[],[f47])).
% 13.31/2.17  fof(f12033,plain,(
% 13.31/2.17    ~r2_hidden(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_3),
% 13.31/2.17    inference(forward_demodulation,[],[f11996,f235])).
% 13.31/2.17  fof(f235,plain,(
% 13.31/2.17    ( ! [X6,X7] : (k5_xboole_0(X6,k3_xboole_0(X7,X6)) = k3_xboole_0(X6,k5_xboole_0(X6,X7))) )),
% 13.31/2.17    inference(forward_demodulation,[],[f221,f54])).
% 13.31/2.17  fof(f54,plain,(
% 13.31/2.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f1])).
% 13.31/2.17  fof(f1,axiom,(
% 13.31/2.17    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 13.31/2.17  fof(f221,plain,(
% 13.31/2.17    ( ! [X6,X7] : (k3_xboole_0(k5_xboole_0(X6,X7),X6) = k5_xboole_0(X6,k3_xboole_0(X7,X6))) )),
% 13.31/2.17    inference(superposition,[],[f65,f129])).
% 13.31/2.17  fof(f129,plain,(
% 13.31/2.17    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f116,f57])).
% 13.31/2.17  fof(f57,plain,(
% 13.31/2.17    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 13.31/2.17    inference(cnf_transformation,[],[f22])).
% 13.31/2.17  fof(f22,plain,(
% 13.31/2.17    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 13.31/2.17    inference(ennf_transformation,[],[f8])).
% 13.31/2.17  fof(f8,axiom,(
% 13.31/2.17    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 13.31/2.17  fof(f116,plain,(
% 13.31/2.17    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 13.31/2.17    inference(equality_resolution,[],[f59])).
% 13.31/2.17  fof(f59,plain,(
% 13.31/2.17    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 13.31/2.17    inference(cnf_transformation,[],[f35])).
% 13.31/2.17  fof(f35,plain,(
% 13.31/2.17    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.31/2.17    inference(flattening,[],[f34])).
% 13.31/2.17  fof(f34,plain,(
% 13.31/2.17    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.31/2.17    inference(nnf_transformation,[],[f4])).
% 13.31/2.17  fof(f4,axiom,(
% 13.31/2.17    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 13.31/2.17  fof(f65,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f7])).
% 13.31/2.17  fof(f7,axiom,(
% 13.31/2.17    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 13.31/2.17  fof(f11996,plain,(
% 13.31/2.17    ~r2_hidden(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_3),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f341,f341,f341,f128])).
% 13.31/2.17  fof(f128,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 13.31/2.17    inference(equality_resolution,[],[f115])).
% 13.31/2.17  fof(f115,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 13.31/2.17    inference(definition_unfolding,[],[f81,f89])).
% 13.31/2.17  fof(f81,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 13.31/2.17    inference(cnf_transformation,[],[f47])).
% 13.31/2.17  fof(f341,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_3),
% 13.31/2.17    inference(avatar_component_clause,[],[f339])).
% 13.31/2.17  fof(f339,plain,(
% 13.31/2.17    spl5_3 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 13.31/2.17  fof(f11980,plain,(
% 13.31/2.17    ~spl5_3 | spl5_1),
% 13.31/2.17    inference(avatar_split_clause,[],[f11527,f295,f339])).
% 13.31/2.17  fof(f295,plain,(
% 13.31/2.17    spl5_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 13.31/2.17  fof(f11527,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_1),
% 13.31/2.17    inference(forward_demodulation,[],[f296,f54])).
% 13.31/2.17  fof(f296,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_1),
% 13.31/2.17    inference(avatar_component_clause,[],[f295])).
% 13.31/2.17  fof(f11790,plain,(
% 13.31/2.17    spl5_2 | spl5_16 | spl5_21),
% 13.31/2.17    inference(avatar_contradiction_clause,[],[f11789])).
% 13.31/2.17  fof(f11789,plain,(
% 13.31/2.17    $false | (spl5_2 | spl5_16 | spl5_21)),
% 13.31/2.17    inference(subsumption_resolution,[],[f11774,f125])).
% 13.31/2.17  fof(f125,plain,(
% 13.31/2.17    ( ! [X2,X0,X5] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2))) )),
% 13.31/2.17    inference(equality_resolution,[],[f124])).
% 13.31/2.17  fof(f124,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X5,X2) != X3) )),
% 13.31/2.17    inference(equality_resolution,[],[f113])).
% 13.31/2.17  fof(f113,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 13.31/2.17    inference(definition_unfolding,[],[f83,f89])).
% 13.31/2.17  fof(f83,plain,(
% 13.31/2.17    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 13.31/2.17    inference(cnf_transformation,[],[f47])).
% 13.31/2.17  fof(f11774,plain,(
% 13.31/2.17    ~r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) | (spl5_2 | spl5_16 | spl5_21)),
% 13.31/2.17    inference(backward_demodulation,[],[f11606,f11711])).
% 13.31/2.17  fof(f11711,plain,(
% 13.31/2.17    ( ! [X0,X1] : (k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))) ) | spl5_2),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f11630,f118])).
% 13.31/2.17  fof(f118,plain,(
% 13.31/2.17    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1)) )),
% 13.31/2.17    inference(equality_resolution,[],[f98])).
% 13.31/2.17  fof(f98,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 13.31/2.17    inference(definition_unfolding,[],[f67,f91,f90])).
% 13.31/2.17  fof(f67,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f24])).
% 13.31/2.17  fof(f11630,plain,(
% 13.31/2.17    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,sK0),sK2))) ) | spl5_2),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f123,f301,f78])).
% 13.31/2.17  fof(f11606,plain,(
% 13.31/2.17    ~r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),k1_xboole_0)) | (spl5_16 | spl5_21)),
% 13.31/2.17    inference(forward_demodulation,[],[f11567,f235])).
% 13.31/2.17  fof(f11567,plain,(
% 13.31/2.17    ~r2_hidden(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)) | (spl5_16 | spl5_21)),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f11536,f11536,f11344,f128])).
% 13.31/2.17  fof(f11344,plain,(
% 13.31/2.17    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl5_16),
% 13.31/2.17    inference(avatar_component_clause,[],[f11343])).
% 13.31/2.17  fof(f11343,plain,(
% 13.31/2.17    spl5_16 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 13.31/2.17  fof(f11536,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_21),
% 13.31/2.17    inference(avatar_component_clause,[],[f11534])).
% 13.31/2.17  fof(f11534,plain,(
% 13.31/2.17    spl5_21 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 13.31/2.17  fof(f11537,plain,(
% 13.31/2.17    ~spl5_21 | spl5_1 | ~spl5_5),
% 13.31/2.17    inference(avatar_split_clause,[],[f11528,f375,f295,f11534])).
% 13.31/2.17  fof(f375,plain,(
% 13.31/2.17    spl5_5 <=> sK0 = sK1),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 13.31/2.17  fof(f11528,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (spl5_1 | ~spl5_5)),
% 13.31/2.17    inference(forward_demodulation,[],[f11527,f376])).
% 13.31/2.17  fof(f376,plain,(
% 13.31/2.17    sK0 = sK1 | ~spl5_5),
% 13.31/2.17    inference(avatar_component_clause,[],[f375])).
% 13.31/2.17  fof(f11483,plain,(
% 13.31/2.17    sK0 != sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 13.31/2.17    introduced(theory_tautology_sat_conflict,[])).
% 13.31/2.17  fof(f11480,plain,(
% 13.31/2.17    ~spl5_16),
% 13.31/2.17    inference(avatar_contradiction_clause,[],[f11479])).
% 13.31/2.17  fof(f11479,plain,(
% 13.31/2.17    $false | ~spl5_16),
% 13.31/2.17    inference(subsumption_resolution,[],[f11478,f127])).
% 13.31/2.17  fof(f11478,plain,(
% 13.31/2.17    ( ! [X39,X38] : (~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,X38,X39))) ) | ~spl5_16),
% 13.31/2.17    inference(forward_demodulation,[],[f11413,f52])).
% 13.31/2.17  fof(f52,plain,(
% 13.31/2.17    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 13.31/2.17    inference(cnf_transformation,[],[f9])).
% 13.31/2.17  fof(f9,axiom,(
% 13.31/2.17    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 13.31/2.17  fof(f11413,plain,(
% 13.31/2.17    ( ! [X39,X38] : (~r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X38,X39),k1_xboole_0))) ) | ~spl5_16),
% 13.31/2.17    inference(superposition,[],[f182,f11345])).
% 13.31/2.17  fof(f11345,plain,(
% 13.31/2.17    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_16),
% 13.31/2.17    inference(avatar_component_clause,[],[f11343])).
% 13.31/2.17  fof(f182,plain,(
% 13.31/2.17    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X3,X4)))) )),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f127,f127,f77])).
% 13.31/2.17  fof(f11381,plain,(
% 13.31/2.17    spl5_16 | ~spl5_13),
% 13.31/2.17    inference(avatar_split_clause,[],[f11050,f11041,f11343])).
% 13.31/2.17  fof(f11041,plain,(
% 13.31/2.17    spl5_13 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 13.31/2.17  fof(f11050,plain,(
% 13.31/2.17    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_13),
% 13.31/2.17    inference(forward_demodulation,[],[f11043,f135])).
% 13.31/2.17  fof(f135,plain,(
% 13.31/2.17    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 13.31/2.17    inference(forward_demodulation,[],[f133,f129])).
% 13.31/2.17  fof(f133,plain,(
% 13.31/2.17    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f116,f96])).
% 13.31/2.17  fof(f96,plain,(
% 13.31/2.17    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 13.31/2.17    inference(definition_unfolding,[],[f62,f56])).
% 13.31/2.17  fof(f56,plain,(
% 13.31/2.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 13.31/2.17    inference(cnf_transformation,[],[f6])).
% 13.31/2.17  fof(f6,axiom,(
% 13.31/2.17    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 13.31/2.17  fof(f62,plain,(
% 13.31/2.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f36])).
% 13.31/2.17  fof(f36,plain,(
% 13.31/2.17    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 13.31/2.17    inference(nnf_transformation,[],[f5])).
% 13.31/2.17  fof(f5,axiom,(
% 13.31/2.17    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 13.31/2.17  fof(f11043,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_13),
% 13.31/2.17    inference(avatar_component_clause,[],[f11041])).
% 13.31/2.17  fof(f11049,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 13.31/2.17    introduced(theory_tautology_sat_conflict,[])).
% 13.31/2.17  fof(f11039,plain,(
% 13.31/2.17    spl5_12 | ~spl5_2 | ~spl5_6),
% 13.31/2.17    inference(avatar_split_clause,[],[f8863,f400,f299,f11036])).
% 13.31/2.17  fof(f11036,plain,(
% 13.31/2.17    spl5_12 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 13.31/2.17  fof(f8863,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | (~spl5_2 | ~spl5_6)),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f300,f401,f101])).
% 13.31/2.17  fof(f101,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | ~r2_hidden(X0,X1)) )),
% 13.31/2.17    inference(definition_unfolding,[],[f69,f90,f90])).
% 13.31/2.17  fof(f69,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f27])).
% 13.31/2.17  fof(f27,plain,(
% 13.31/2.17    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 13.31/2.17    inference(flattening,[],[f26])).
% 13.31/2.17  fof(f26,plain,(
% 13.31/2.17    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 13.31/2.17    inference(ennf_transformation,[],[f16])).
% 13.31/2.17  fof(f16,axiom,(
% 13.31/2.17    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 13.31/2.17  fof(f300,plain,(
% 13.31/2.17    r2_hidden(sK0,sK2) | ~spl5_2),
% 13.31/2.17    inference(avatar_component_clause,[],[f299])).
% 13.31/2.17  fof(f11029,plain,(
% 13.31/2.17    spl5_10 | ~spl5_2),
% 13.31/2.17    inference(avatar_split_clause,[],[f8775,f299,f11026])).
% 13.31/2.17  fof(f11026,plain,(
% 13.31/2.17    spl5_10 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 13.31/2.17  fof(f8775,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) | ~spl5_2),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f300,f118])).
% 13.31/2.17  fof(f8736,plain,(
% 13.31/2.17    ~spl5_3 | spl5_6 | spl5_8),
% 13.31/2.17    inference(avatar_contradiction_clause,[],[f8735])).
% 13.31/2.17  fof(f8735,plain,(
% 13.31/2.17    $false | (~spl5_3 | spl5_6 | spl5_8)),
% 13.31/2.17    inference(subsumption_resolution,[],[f8734,f123])).
% 13.31/2.17  fof(f8734,plain,(
% 13.31/2.17    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | (~spl5_3 | spl5_6 | spl5_8)),
% 13.31/2.17    inference(subsumption_resolution,[],[f8720,f727])).
% 13.31/2.17  fof(f727,plain,(
% 13.31/2.17    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_8),
% 13.31/2.17    inference(avatar_component_clause,[],[f725])).
% 13.31/2.17  fof(f725,plain,(
% 13.31/2.17    spl5_8 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 13.31/2.17    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 13.31/2.17  fof(f8720,plain,(
% 13.31/2.17    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | (~spl5_3 | spl5_6)),
% 13.31/2.17    inference(resolution,[],[f478,f679])).
% 13.31/2.17  fof(f679,plain,(
% 13.31/2.17    ( ! [X0] : (~r2_hidden(sK1,k3_xboole_0(sK2,X0))) ) | spl5_6),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f402,f417,f79])).
% 13.31/2.17  fof(f79,plain,(
% 13.31/2.17    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 13.31/2.17    inference(cnf_transformation,[],[f42])).
% 13.31/2.17  fof(f417,plain,(
% 13.31/2.17    ( ! [X0] : (~r2_hidden(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) ) | spl5_6),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f402,f121])).
% 13.31/2.17  fof(f121,plain,(
% 13.31/2.17    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 13.31/2.17    inference(equality_resolution,[],[f107])).
% 13.31/2.17  fof(f107,plain,(
% 13.31/2.17    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 13.31/2.17    inference(definition_unfolding,[],[f70,f56])).
% 13.31/2.17  fof(f70,plain,(
% 13.31/2.17    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 13.31/2.17    inference(cnf_transformation,[],[f41])).
% 13.31/2.17  fof(f41,plain,(
% 13.31/2.17    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.31/2.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 13.31/2.17  fof(f40,plain,(
% 13.31/2.17    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 13.31/2.17    introduced(choice_axiom,[])).
% 13.31/2.17  fof(f39,plain,(
% 13.31/2.17    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.31/2.17    inference(rectify,[],[f38])).
% 13.31/2.17  fof(f38,plain,(
% 13.31/2.17    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.31/2.17    inference(flattening,[],[f37])).
% 13.31/2.17  fof(f37,plain,(
% 13.31/2.17    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 13.31/2.17    inference(nnf_transformation,[],[f2])).
% 13.31/2.17  fof(f2,axiom,(
% 13.31/2.17    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 13.31/2.17  fof(f402,plain,(
% 13.31/2.17    ~r2_hidden(sK1,sK2) | spl5_6),
% 13.31/2.17    inference(avatar_component_clause,[],[f400])).
% 13.31/2.17  fof(f478,plain,(
% 13.31/2.17    ( ! [X1] : (r2_hidden(X1,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ) | ~spl5_3),
% 13.31/2.17    inference(superposition,[],[f78,f340])).
% 13.31/2.17  fof(f340,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_3),
% 13.31/2.17    inference(avatar_component_clause,[],[f339])).
% 13.31/2.17  fof(f728,plain,(
% 13.31/2.17    ~spl5_8 | spl5_5),
% 13.31/2.17    inference(avatar_split_clause,[],[f385,f375,f725])).
% 13.31/2.17  fof(f385,plain,(
% 13.31/2.17    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_5),
% 13.31/2.17    inference(unit_resulting_resolution,[],[f377,f377,f377,f128])).
% 13.31/2.17  fof(f377,plain,(
% 13.31/2.17    sK0 != sK1 | spl5_5),
% 13.31/2.17    inference(avatar_component_clause,[],[f375])).
% 13.31/2.17  fof(f476,plain,(
% 13.31/2.17    spl5_3 | ~spl5_1),
% 13.31/2.17    inference(avatar_split_clause,[],[f473,f295,f339])).
% 13.31/2.17  fof(f473,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_1),
% 13.31/2.17    inference(forward_demodulation,[],[f297,f54])).
% 13.31/2.17  fof(f297,plain,(
% 13.31/2.17    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl5_1),
% 13.31/2.17    inference(avatar_component_clause,[],[f295])).
% 13.31/2.17  fof(f472,plain,(
% 13.31/2.17    spl5_1 | spl5_6 | spl5_5),
% 13.31/2.17    inference(avatar_split_clause,[],[f94,f375,f400,f295])).
% 13.31/2.17  fof(f94,plain,(
% 13.31/2.17    sK0 = sK1 | r2_hidden(sK1,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 13.31/2.17    inference(definition_unfolding,[],[f49,f91,f56,f90])).
% 13.31/2.17  fof(f49,plain,(
% 13.31/2.17    sK0 = sK1 | r2_hidden(sK1,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.31/2.17    inference(cnf_transformation,[],[f33])).
% 13.31/2.17  fof(f33,plain,(
% 13.31/2.17    ((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 13.31/2.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).
% 13.31/2.17  fof(f32,plain,(
% 13.31/2.17    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => (((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 13.31/2.17    introduced(choice_axiom,[])).
% 13.31/2.17  fof(f31,plain,(
% 13.31/2.17    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 13.31/2.17    inference(flattening,[],[f30])).
% 13.31/2.17  fof(f30,plain,(
% 13.31/2.17    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 13.31/2.17    inference(nnf_transformation,[],[f21])).
% 13.31/2.17  fof(f21,plain,(
% 13.31/2.17    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 13.31/2.17    inference(ennf_transformation,[],[f20])).
% 13.31/2.17  fof(f20,negated_conjecture,(
% 13.31/2.17    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 13.31/2.17    inference(negated_conjecture,[],[f19])).
% 13.31/2.17  fof(f19,conjecture,(
% 13.31/2.17    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 13.31/2.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 13.31/2.17  fof(f403,plain,(
% 13.31/2.17    ~spl5_1 | spl5_2 | ~spl5_6),
% 13.31/2.17    inference(avatar_split_clause,[],[f93,f400,f299,f295])).
% 13.31/2.17  fof(f93,plain,(
% 13.31/2.17    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 13.31/2.17    inference(definition_unfolding,[],[f50,f91,f56,f90])).
% 13.31/2.17  fof(f50,plain,(
% 13.31/2.17    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.31/2.17    inference(cnf_transformation,[],[f33])).
% 13.31/2.17  fof(f378,plain,(
% 13.31/2.17    ~spl5_1 | spl5_2 | ~spl5_5),
% 13.31/2.17    inference(avatar_split_clause,[],[f92,f375,f299,f295])).
% 13.31/2.17  fof(f92,plain,(
% 13.31/2.17    sK0 != sK1 | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 13.31/2.17    inference(definition_unfolding,[],[f51,f91,f56,f90])).
% 13.31/2.17  fof(f51,plain,(
% 13.31/2.17    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.31/2.17    inference(cnf_transformation,[],[f33])).
% 13.31/2.17  fof(f302,plain,(
% 13.31/2.17    spl5_1 | ~spl5_2),
% 13.31/2.17    inference(avatar_split_clause,[],[f95,f299,f295])).
% 13.31/2.17  fof(f95,plain,(
% 13.31/2.17    ~r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 13.31/2.17    inference(definition_unfolding,[],[f48,f91,f56,f90])).
% 13.31/2.17  fof(f48,plain,(
% 13.31/2.17    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.31/2.17    inference(cnf_transformation,[],[f33])).
% 13.31/2.17  % SZS output end Proof for theBenchmark
% 13.31/2.17  % (19482)------------------------------
% 13.31/2.17  % (19482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.31/2.17  % (19482)Termination reason: Refutation
% 13.31/2.17  
% 13.31/2.17  % (19482)Memory used [KB]: 20724
% 13.31/2.17  % (19482)Time elapsed: 1.719 s
% 13.31/2.17  % (19482)------------------------------
% 13.31/2.17  % (19482)------------------------------
% 14.29/2.18  % (19461)Success in time 1.811 s
%------------------------------------------------------------------------------
