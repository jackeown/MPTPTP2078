%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 ( 333 expanded)
%              Number of equality atoms :  150 ( 206 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f664,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f133,f138,f658,f663])).

fof(f663,plain,
    ( spl7_1
    | spl7_2
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | spl7_1
    | spl7_2
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f132,f127,f657,f122])).

fof(f122,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f65,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f657,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f655])).

fof(f655,plain,
    ( spl7_11
  <=> r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f127,plain,
    ( sK0 != sK2
    | spl7_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f132,plain,
    ( sK0 != sK3
    | spl7_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f658,plain,
    ( spl7_11
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f650,f135,f655])).

fof(f135,plain,
    ( spl7_3
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f650,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f484,f137])).

fof(f137,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f484,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_tarski(k2_enumset1(X11,X11,X11,X12),X13)
      | r2_hidden(X11,X13) ) ),
    inference(global_subsumption,[],[f339,f431])).

fof(f431,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(k1_tarski(X7),X8)
      | r2_hidden(X7,X8) ) ),
    inference(global_subsumption,[],[f217,f422])).

fof(f422,plain,(
    ! [X8,X7] :
      ( k1_tarski(X7) = k5_xboole_0(k1_tarski(X7),k1_tarski(X7))
      | r2_hidden(X7,X8)
      | ~ r1_tarski(k1_tarski(X7),X8) ) ),
    inference(superposition,[],[f392,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f392,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),X2))
      | r2_hidden(X1,X2) ) ),
    inference(forward_demodulation,[],[f117,f92])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f90])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f117,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2))
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f64,f80,f90])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f217,plain,(
    ! [X1] : k1_tarski(X1) != k5_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f123,f82])).

fof(f82,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f123,plain,(
    ! [X1] : k1_tarski(X1) != k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X1))) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f74,f80])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f339,plain,(
    ! [X12,X10,X11] :
      ( r1_tarski(k1_tarski(X10),X11)
      | ~ r1_tarski(k2_enumset1(X10,X10,X10,X12),X11) ) ),
    inference(resolution,[],[f163,f115])).

fof(f115,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f163,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | r1_tarski(X4,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f140,f60])).

fof(f140,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k3_xboole_0(X3,X2))
      | r1_tarski(X4,X2) ) ),
    inference(superposition,[],[f59,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f138,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f94,f135])).

fof(f94,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f51,f90,f90])).

fof(f51,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f133,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f53,f130])).

fof(f53,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f128,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f52,f125])).

fof(f52,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:02:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (6601)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (6615)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (6608)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (6607)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (6623)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (6616)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (6605)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (6612)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (6600)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (6616)Refutation not found, incomplete strategy% (6616)------------------------------
% 0.20/0.53  % (6616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6616)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6616)Memory used [KB]: 10618
% 0.20/0.53  % (6616)Time elapsed: 0.118 s
% 0.20/0.53  % (6616)------------------------------
% 0.20/0.53  % (6616)------------------------------
% 0.20/0.53  % (6603)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (6624)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (6613)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (6614)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (6629)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (6602)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (6604)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (6629)Refutation not found, incomplete strategy% (6629)------------------------------
% 0.20/0.54  % (6629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6629)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6629)Memory used [KB]: 1663
% 0.20/0.54  % (6629)Time elapsed: 0.129 s
% 0.20/0.54  % (6629)------------------------------
% 0.20/0.54  % (6629)------------------------------
% 0.20/0.54  % (6625)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (6627)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (6606)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (6618)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (6621)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (6619)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (6617)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (6622)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (6623)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (6609)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (6610)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (6628)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (6611)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (6626)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (6620)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f664,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f128,f133,f138,f658,f663])).
% 0.20/0.57  fof(f663,plain,(
% 0.20/0.57    spl7_1 | spl7_2 | ~spl7_11),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f659])).
% 0.20/0.57  fof(f659,plain,(
% 0.20/0.57    $false | (spl7_1 | spl7_2 | ~spl7_11)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f132,f127,f657,f122])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.57    inference(equality_resolution,[],[f109])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.57    inference(definition_unfolding,[],[f65,f90])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f71,f86])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(rectify,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(flattening,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.57    inference(nnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.57  fof(f657,plain,(
% 0.20/0.57    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f655])).
% 0.20/0.57  fof(f655,plain,(
% 0.20/0.57    spl7_11 <=> r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    sK0 != sK2 | spl7_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f125])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    spl7_1 <=> sK0 = sK2),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    sK0 != sK3 | spl7_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f130])).
% 0.20/0.57  fof(f130,plain,(
% 0.20/0.57    spl7_2 <=> sK0 = sK3),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.57  fof(f658,plain,(
% 0.20/0.57    spl7_11 | ~spl7_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f650,f135,f655])).
% 0.20/0.57  fof(f135,plain,(
% 0.20/0.57    spl7_3 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.57  fof(f650,plain,(
% 0.20/0.57    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_3),
% 0.20/0.57    inference(resolution,[],[f484,f137])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f135])).
% 0.20/0.57  fof(f484,plain,(
% 0.20/0.57    ( ! [X12,X13,X11] : (~r1_tarski(k2_enumset1(X11,X11,X11,X12),X13) | r2_hidden(X11,X13)) )),
% 0.20/0.57    inference(global_subsumption,[],[f339,f431])).
% 0.20/0.57  fof(f431,plain,(
% 0.20/0.57    ( ! [X8,X7] : (~r1_tarski(k1_tarski(X7),X8) | r2_hidden(X7,X8)) )),
% 0.20/0.57    inference(global_subsumption,[],[f217,f422])).
% 0.20/0.57  fof(f422,plain,(
% 0.20/0.57    ( ! [X8,X7] : (k1_tarski(X7) = k5_xboole_0(k1_tarski(X7),k1_tarski(X7)) | r2_hidden(X7,X8) | ~r1_tarski(k1_tarski(X7),X8)) )),
% 0.20/0.57    inference(superposition,[],[f392,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.57  fof(f392,plain,(
% 0.20/0.57    ( ! [X2,X1] : (k1_tarski(X1) = k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),X2)) | r2_hidden(X1,X2)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f117,f92])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f72,f90])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    ( ! [X2,X1] : (k1_tarski(X1) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) | r2_hidden(X1,X2)) )),
% 0.20/0.57    inference(equality_resolution,[],[f100])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_tarski(X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f64,f80,f90])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.57    inference(flattening,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.57    inference(nnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.20/0.57  fof(f217,plain,(
% 0.20/0.57    ( ! [X1] : (k1_tarski(X1) != k5_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.57    inference(forward_demodulation,[],[f123,f82])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.57    inference(rectify,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    ( ! [X1] : (k1_tarski(X1) != k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X1)))) )),
% 0.20/0.57    inference(equality_resolution,[],[f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f74,f80])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.57  fof(f339,plain,(
% 0.20/0.57    ( ! [X12,X10,X11] : (r1_tarski(k1_tarski(X10),X11) | ~r1_tarski(k2_enumset1(X10,X10,X10,X12),X11)) )),
% 0.20/0.57    inference(resolution,[],[f163,f115])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_enumset1(X1,X1,X1,X2))) )),
% 0.20/0.57    inference(equality_resolution,[],[f97])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k1_tarski(X1) != X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f56,f90])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.57    inference(flattening,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.57    inference(nnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.20/0.57  fof(f163,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | r1_tarski(X4,X3) | ~r1_tarski(X2,X3)) )),
% 0.20/0.57    inference(superposition,[],[f140,f60])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (~r1_tarski(X4,k3_xboole_0(X3,X2)) | r1_tarski(X4,X2)) )),
% 0.20/0.57    inference(superposition,[],[f59,f81])).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    spl7_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f94,f135])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.20/0.57    inference(definition_unfolding,[],[f51,f90,f90])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.57    inference(ennf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.57    inference(negated_conjecture,[],[f25])).
% 0.20/0.57  fof(f25,conjecture,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.20/0.57  fof(f133,plain,(
% 0.20/0.57    ~spl7_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f53,f130])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    sK0 != sK3),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f128,plain,(
% 0.20/0.57    ~spl7_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f52,f125])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    sK0 != sK2),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (6623)------------------------------
% 0.20/0.57  % (6623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (6623)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (6623)Memory used [KB]: 11385
% 0.20/0.57  % (6623)Time elapsed: 0.144 s
% 0.20/0.57  % (6623)------------------------------
% 0.20/0.57  % (6623)------------------------------
% 0.20/0.57  % (6599)Success in time 0.207 s
%------------------------------------------------------------------------------
