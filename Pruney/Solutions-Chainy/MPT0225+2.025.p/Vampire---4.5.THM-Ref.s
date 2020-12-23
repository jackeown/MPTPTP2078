%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:09 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 260 expanded)
%              Number of leaves         :   22 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  289 ( 654 expanded)
%              Number of equality atoms :  158 ( 360 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f102,f182,f188,f196,f205,f242,f249])).

fof(f249,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f60,f219,f111])).

fof(f111,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(forward_demodulation,[],[f110,f45])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0))
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f81,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f105,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f105,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    inference(global_subsumption,[],[f60,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f81,f45])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f219,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_6
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f60,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f242,plain,
    ( spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f210,f202,f217])).

fof(f202,plain,
    ( spl6_5
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f210,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_5 ),
    inference(superposition,[],[f87,f204])).

fof(f204,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f202])).

fof(f87,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f205,plain,
    ( spl6_5
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f200,f98,f94,f202])).

fof(f94,plain,
    ( spl6_1
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f98,plain,
    ( spl6_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f200,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f199,f106])).

fof(f199,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f95,f100])).

fof(f100,plain,
    ( sK0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f95,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f196,plain,
    ( spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f99,f99,f99,f187,f92])).

fof(f92,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f187,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f99,plain,
    ( sK0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f188,plain,
    ( spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f183,f179,f185])).

fof(f179,plain,
    ( spl6_3
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f183,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_3 ),
    inference(resolution,[],[f181,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f181,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f182,plain,
    ( ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f173,f94,f179])).

fof(f173,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_1 ),
    inference(superposition,[],[f96,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f134,f135])).

fof(f135,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f131,f106])).

fof(f131,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f65,f45])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f59,f44])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f134,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f65,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f81,f58])).

fof(f96,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f102,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f67,f98,f94])).

% (6552)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f67,plain,
    ( sK0 != sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f38,f64,f64,f64])).

fof(f38,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f101,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f66,f98,f94])).

fof(f66,plain,
    ( sK0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f39,f64,f64,f64])).

fof(f39,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.46/0.57  % (6547)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.76/0.59  % (6570)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.76/0.59  % (6562)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.76/0.59  % (6551)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.76/0.59  % (6558)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.76/0.60  % (6566)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.76/0.60  % (6554)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.76/0.60  % (6553)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.76/0.60  % (6555)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.76/0.60  % (6570)Refutation found. Thanks to Tanya!
% 1.76/0.60  % SZS status Theorem for theBenchmark
% 1.76/0.60  % (6556)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.76/0.60  % SZS output start Proof for theBenchmark
% 1.76/0.60  fof(f250,plain,(
% 1.76/0.60    $false),
% 1.76/0.60    inference(avatar_sat_refutation,[],[f101,f102,f182,f188,f196,f205,f242,f249])).
% 1.76/0.60  fof(f249,plain,(
% 1.76/0.60    ~spl6_6),
% 1.76/0.60    inference(avatar_contradiction_clause,[],[f244])).
% 1.76/0.60  fof(f244,plain,(
% 1.76/0.60    $false | ~spl6_6),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f60,f219,f111])).
% 1.76/0.60  fof(f111,plain,(
% 1.76/0.60    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) )),
% 1.76/0.60    inference(forward_demodulation,[],[f110,f45])).
% 1.76/0.60  fof(f45,plain,(
% 1.76/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.76/0.60    inference(cnf_transformation,[],[f4])).
% 1.76/0.60  fof(f4,axiom,(
% 1.76/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.76/0.60  fof(f110,plain,(
% 1.76/0.60    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0)) | ~r1_xboole_0(X2,X2)) )),
% 1.76/0.60    inference(superposition,[],[f81,f106])).
% 1.76/0.60  fof(f106,plain,(
% 1.76/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.76/0.60    inference(resolution,[],[f105,f58])).
% 1.76/0.60  fof(f58,plain,(
% 1.76/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.76/0.60    inference(cnf_transformation,[],[f37])).
% 1.76/0.61  fof(f37,plain,(
% 1.76/0.61    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f36])).
% 1.76/0.61  fof(f36,plain,(
% 1.76/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f21,plain,(
% 1.76/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.76/0.61    inference(ennf_transformation,[],[f2])).
% 1.76/0.61  fof(f2,axiom,(
% 1.76/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.76/0.61  fof(f105,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 1.76/0.61    inference(global_subsumption,[],[f60,f104])).
% 1.76/0.61  fof(f104,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.76/0.61    inference(superposition,[],[f81,f45])).
% 1.76/0.61  fof(f81,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.76/0.61    inference(definition_unfolding,[],[f57,f44])).
% 1.76/0.61  fof(f44,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f5])).
% 1.76/0.61  fof(f5,axiom,(
% 1.76/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.76/0.61  fof(f57,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f35])).
% 1.76/0.61  fof(f35,plain,(
% 1.76/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f34])).
% 1.76/0.61  fof(f34,plain,(
% 1.76/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f20,plain,(
% 1.76/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.76/0.61    inference(ennf_transformation,[],[f16])).
% 1.76/0.61  fof(f16,plain,(
% 1.76/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.76/0.61    inference(rectify,[],[f1])).
% 1.76/0.61  fof(f1,axiom,(
% 1.76/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.76/0.61  fof(f219,plain,(
% 1.76/0.61    r2_hidden(sK0,k1_xboole_0) | ~spl6_6),
% 1.76/0.61    inference(avatar_component_clause,[],[f217])).
% 1.76/0.61  fof(f217,plain,(
% 1.76/0.61    spl6_6 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.76/0.61  fof(f60,plain,(
% 1.76/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f6])).
% 1.76/0.61  fof(f6,axiom,(
% 1.76/0.61    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.76/0.61  fof(f242,plain,(
% 1.76/0.61    spl6_6 | ~spl6_5),
% 1.76/0.61    inference(avatar_split_clause,[],[f210,f202,f217])).
% 1.76/0.61  fof(f202,plain,(
% 1.76/0.61    spl6_5 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.76/0.61  fof(f210,plain,(
% 1.76/0.61    r2_hidden(sK0,k1_xboole_0) | ~spl6_5),
% 1.76/0.61    inference(superposition,[],[f87,f204])).
% 1.76/0.61  fof(f204,plain,(
% 1.76/0.61    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_5),
% 1.76/0.61    inference(avatar_component_clause,[],[f202])).
% 1.76/0.61  fof(f87,plain,(
% 1.76/0.61    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.76/0.61    inference(equality_resolution,[],[f86])).
% 1.76/0.61  fof(f86,plain,(
% 1.76/0.61    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.76/0.61    inference(equality_resolution,[],[f77])).
% 1.76/0.61  fof(f77,plain,(
% 1.76/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.76/0.61    inference(definition_unfolding,[],[f51,f62])).
% 1.76/0.61  fof(f62,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f11])).
% 1.76/0.61  fof(f11,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.76/0.61  fof(f51,plain,(
% 1.76/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.76/0.61    inference(cnf_transformation,[],[f33])).
% 1.76/0.61  fof(f33,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.76/0.61  fof(f32,plain,(
% 1.76/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f31,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.76/0.61    inference(rectify,[],[f30])).
% 1.76/0.61  fof(f30,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.76/0.61    inference(flattening,[],[f29])).
% 1.76/0.61  fof(f29,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.76/0.61    inference(nnf_transformation,[],[f19])).
% 1.76/0.61  fof(f19,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.76/0.61    inference(ennf_transformation,[],[f7])).
% 1.76/0.61  fof(f7,axiom,(
% 1.76/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.76/0.61  fof(f205,plain,(
% 1.76/0.61    spl6_5 | ~spl6_1 | ~spl6_2),
% 1.76/0.61    inference(avatar_split_clause,[],[f200,f98,f94,f202])).
% 1.76/0.61  fof(f94,plain,(
% 1.76/0.61    spl6_1 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.76/0.61  fof(f98,plain,(
% 1.76/0.61    spl6_2 <=> sK0 = sK1),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.76/0.61  fof(f200,plain,(
% 1.76/0.61    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl6_1 | ~spl6_2)),
% 1.76/0.61    inference(forward_demodulation,[],[f199,f106])).
% 1.76/0.61  fof(f199,plain,(
% 1.76/0.61    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl6_1 | ~spl6_2)),
% 1.76/0.61    inference(forward_demodulation,[],[f95,f100])).
% 1.76/0.61  fof(f100,plain,(
% 1.76/0.61    sK0 = sK1 | ~spl6_2),
% 1.76/0.61    inference(avatar_component_clause,[],[f98])).
% 1.76/0.61  fof(f95,plain,(
% 1.76/0.61    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_1),
% 1.76/0.61    inference(avatar_component_clause,[],[f94])).
% 1.76/0.61  fof(f196,plain,(
% 1.76/0.61    spl6_2 | ~spl6_4),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f190])).
% 1.76/0.61  fof(f190,plain,(
% 1.76/0.61    $false | (spl6_2 | ~spl6_4)),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f99,f99,f99,f187,f92])).
% 1.76/0.61  fof(f92,plain,(
% 1.76/0.61    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.76/0.61    inference(equality_resolution,[],[f80])).
% 1.76/0.61  fof(f80,plain,(
% 1.76/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.76/0.61    inference(definition_unfolding,[],[f48,f62])).
% 1.76/0.61  fof(f48,plain,(
% 1.76/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.76/0.61    inference(cnf_transformation,[],[f33])).
% 1.76/0.61  fof(f187,plain,(
% 1.76/0.61    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_4),
% 1.76/0.61    inference(avatar_component_clause,[],[f185])).
% 1.76/0.61  fof(f185,plain,(
% 1.76/0.61    spl6_4 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.76/0.61  fof(f99,plain,(
% 1.76/0.61    sK0 != sK1 | spl6_2),
% 1.76/0.61    inference(avatar_component_clause,[],[f98])).
% 1.76/0.61  fof(f188,plain,(
% 1.76/0.61    spl6_4 | spl6_3),
% 1.76/0.61    inference(avatar_split_clause,[],[f183,f179,f185])).
% 1.76/0.61  fof(f179,plain,(
% 1.76/0.61    spl6_3 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.76/0.61  fof(f183,plain,(
% 1.76/0.61    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_3),
% 1.76/0.61    inference(resolution,[],[f181,f72])).
% 1.76/0.61  fof(f72,plain,(
% 1.76/0.61    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.76/0.61    inference(definition_unfolding,[],[f46,f64])).
% 1.76/0.61  fof(f64,plain,(
% 1.76/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.76/0.61    inference(definition_unfolding,[],[f47,f63])).
% 1.76/0.61  fof(f63,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.76/0.61    inference(definition_unfolding,[],[f61,f62])).
% 1.76/0.61  fof(f61,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f10])).
% 1.76/0.61  fof(f10,axiom,(
% 1.76/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.76/0.61  fof(f47,plain,(
% 1.76/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f9])).
% 1.76/0.61  fof(f9,axiom,(
% 1.76/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.76/0.61  fof(f46,plain,(
% 1.76/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f18])).
% 1.76/0.61  fof(f18,plain,(
% 1.76/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.76/0.61    inference(ennf_transformation,[],[f13])).
% 1.76/0.61  fof(f13,axiom,(
% 1.76/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.76/0.61  fof(f181,plain,(
% 1.76/0.61    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_3),
% 1.76/0.61    inference(avatar_component_clause,[],[f179])).
% 1.76/0.61  fof(f182,plain,(
% 1.76/0.61    ~spl6_3 | spl6_1),
% 1.76/0.61    inference(avatar_split_clause,[],[f173,f94,f179])).
% 1.76/0.61  fof(f173,plain,(
% 1.76/0.61    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_1),
% 1.76/0.61    inference(trivial_inequality_removal,[],[f172])).
% 1.76/0.61  fof(f172,plain,(
% 1.76/0.61    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_1),
% 1.76/0.61    inference(superposition,[],[f96,f159])).
% 1.76/0.61  fof(f159,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.76/0.61    inference(forward_demodulation,[],[f134,f135])).
% 1.76/0.61  fof(f135,plain,(
% 1.76/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.76/0.61    inference(forward_demodulation,[],[f131,f106])).
% 1.76/0.61  fof(f131,plain,(
% 1.76/0.61    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.76/0.61    inference(superposition,[],[f65,f45])).
% 1.76/0.61  fof(f65,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.76/0.61    inference(definition_unfolding,[],[f59,f44])).
% 1.76/0.61  fof(f59,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f3])).
% 1.76/0.61  fof(f3,axiom,(
% 1.76/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.76/0.61  fof(f134,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 1.76/0.61    inference(superposition,[],[f65,f103])).
% 1.76/0.61  fof(f103,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.76/0.61    inference(resolution,[],[f81,f58])).
% 1.76/0.61  fof(f96,plain,(
% 1.76/0.61    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_1),
% 1.76/0.61    inference(avatar_component_clause,[],[f94])).
% 1.76/0.61  fof(f102,plain,(
% 1.76/0.61    spl6_1 | ~spl6_2),
% 1.76/0.61    inference(avatar_split_clause,[],[f67,f98,f94])).
% 1.76/0.61  % (6552)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.76/0.61  fof(f67,plain,(
% 1.76/0.61    sK0 != sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.76/0.61    inference(definition_unfolding,[],[f38,f64,f64,f64])).
% 1.76/0.61  fof(f38,plain,(
% 1.76/0.61    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  fof(f24,plain,(
% 1.76/0.61    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.76/0.61  fof(f23,plain,(
% 1.76/0.61    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f22,plain,(
% 1.76/0.61    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.76/0.61    inference(nnf_transformation,[],[f17])).
% 1.76/0.61  fof(f17,plain,(
% 1.76/0.61    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.76/0.61    inference(ennf_transformation,[],[f15])).
% 1.76/0.61  fof(f15,negated_conjecture,(
% 1.76/0.61    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.76/0.61    inference(negated_conjecture,[],[f14])).
% 1.76/0.61  fof(f14,conjecture,(
% 1.76/0.61    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.76/0.61  fof(f101,plain,(
% 1.76/0.61    ~spl6_1 | spl6_2),
% 1.76/0.61    inference(avatar_split_clause,[],[f66,f98,f94])).
% 1.76/0.61  fof(f66,plain,(
% 1.76/0.61    sK0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.76/0.61    inference(definition_unfolding,[],[f39,f64,f64,f64])).
% 1.76/0.61  fof(f39,plain,(
% 1.76/0.61    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.76/0.61    inference(cnf_transformation,[],[f24])).
% 1.76/0.61  % SZS output end Proof for theBenchmark
% 1.76/0.61  % (6570)------------------------------
% 1.76/0.61  % (6570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.61  % (6570)Termination reason: Refutation
% 1.76/0.61  
% 1.76/0.61  % (6570)Memory used [KB]: 10874
% 1.76/0.61  % (6570)Time elapsed: 0.116 s
% 1.76/0.61  % (6570)------------------------------
% 1.76/0.61  % (6570)------------------------------
% 1.76/0.61  % (6546)Success in time 0.251 s
%------------------------------------------------------------------------------
