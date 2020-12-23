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
% DateTime   : Thu Dec  3 12:58:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 203 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 ( 823 expanded)
%              Number of equality atoms :  156 ( 474 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f153,f201])).

fof(f201,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f194,f90])).

fof(f90,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

% (22928)Termination reason: Refutation not found, incomplete strategy

% (22928)Memory used [KB]: 1791
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

% (22928)Time elapsed: 0.140 s
% (22928)------------------------------
% (22928)------------------------------
fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f194,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_1 ),
    inference(superposition,[],[f92,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f182,f65])).

fof(f65,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (22941)Refutation not found, incomplete strategy% (22941)------------------------------
% (22941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22941)Termination reason: Refutation not found, incomplete strategy

% (22941)Memory used [KB]: 6140
% (22941)Time elapsed: 0.135 s
% (22941)------------------------------
% (22941)------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f181,f66])).

fof(f66,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f181,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl7_1 ),
    inference(superposition,[],[f162,f97])).

fof(f97,plain,(
    ! [X3] :
      ( sK4(k2_tarski(X3,X3)) = X3
      | k1_xboole_0 = k2_tarski(X3,X3) ) ),
    inference(resolution,[],[f66,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f162,plain,
    ( ! [X1] :
        ( sK1 != sK4(X1)
        | ~ r2_hidden(sK1,X1)
        | k1_xboole_0 = X1 )
    | ~ spl7_1 ),
    inference(superposition,[],[f40,f158])).

fof(f158,plain,
    ( sK1 = k4_tarski(sK1,sK3)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f35,f154])).

fof(f154,plain,
    ( sK1 = sK2
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f82,f73])).

fof(f73,plain,
    ( sK1 = k1_mcart_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_1
  <=> sK1 = k1_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f82,plain,(
    k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f35,plain,(
    sK1 = k4_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK1 = k2_mcart_1(sK1)
      | sK1 = k1_mcart_1(sK1) )
    & sK1 = k4_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK1 = k2_mcart_1(sK1)
        | sK1 = k1_mcart_1(sK1) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK1 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK1
   => sK1 = k4_tarski(sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f67,f69])).

fof(f69,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f17])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f67,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f153,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f146,f90])).

fof(f146,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f92,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f135,f65])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f134,f66])).

fof(f134,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl7_2 ),
    inference(superposition,[],[f128,f97])).

fof(f128,plain,
    ( ! [X0] :
        ( sK1 != sK4(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_2 ),
    inference(superposition,[],[f41,f85])).

fof(f85,plain,
    ( sK1 = k4_tarski(sK2,sK1)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f35,f84])).

fof(f84,plain,
    ( sK1 = sK3
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f83,f77])).

fof(f77,plain,
    ( sK1 = k2_mcart_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_2
  <=> sK1 = k2_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f83,plain,(
    k2_mcart_1(sK1) = sK3 ),
    inference(superposition,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f36,f75,f71])).

fof(f36,plain,
    ( sK1 = k2_mcart_1(sK1)
    | sK1 = k1_mcart_1(sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (22928)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (22920)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (22941)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (22920)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (22933)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (22925)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (22936)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (22925)Refutation not found, incomplete strategy% (22925)------------------------------
% 0.22/0.57  % (22925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (22925)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  % (22928)Refutation not found, incomplete strategy% (22928)------------------------------
% 0.22/0.57  % (22928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  
% 0.22/0.57  % (22925)Memory used [KB]: 6268
% 0.22/0.57  % (22925)Time elapsed: 0.133 s
% 0.22/0.57  % (22925)------------------------------
% 0.22/0.57  % (22925)------------------------------
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f202,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f78,f153,f201])).
% 0.22/0.57  fof(f201,plain,(
% 0.22/0.57    ~spl7_1),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f200])).
% 0.22/0.57  fof(f200,plain,(
% 0.22/0.57    $false | ~spl7_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f194,f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(resolution,[],[f88,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(resolution,[],[f48,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  % (22928)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (22928)Memory used [KB]: 1791
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.57  % (22928)Time elapsed: 0.140 s
% 0.22/0.57  % (22928)------------------------------
% 0.22/0.57  % (22928)------------------------------
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.57    inference(nnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    r2_hidden(sK1,k1_xboole_0) | ~spl7_1),
% 0.22/0.57    inference(superposition,[],[f92,f185])).
% 0.22/0.57  fof(f185,plain,(
% 0.22/0.57    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl7_1),
% 0.22/0.57    inference(resolution,[],[f182,f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.22/0.57    inference(equality_resolution,[],[f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.22/0.57    inference(equality_resolution,[],[f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.22/0.57    inference(definition_unfolding,[],[f45,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.57    inference(rectify,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  % (22941)Refutation not found, incomplete strategy% (22941)------------------------------
% 0.22/0.57  % (22941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (22941)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (22941)Memory used [KB]: 6140
% 0.22/0.57  % (22941)Time elapsed: 0.135 s
% 0.22/0.57  % (22941)------------------------------
% 0.22/0.57  % (22941)------------------------------
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.58  fof(f182,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl7_1),
% 0.22/0.58    inference(subsumption_resolution,[],[f181,f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.22/0.58    inference(equality_resolution,[],[f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.22/0.58    inference(definition_unfolding,[],[f44,f38])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl7_1),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f180])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0 | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl7_1),
% 0.22/0.58    inference(superposition,[],[f162,f97])).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    ( ! [X3] : (sK4(k2_tarski(X3,X3)) = X3 | k1_xboole_0 = k2_tarski(X3,X3)) )),
% 0.22/0.58    inference(resolution,[],[f66,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.58  fof(f162,plain,(
% 0.22/0.58    ( ! [X1] : (sK1 != sK4(X1) | ~r2_hidden(sK1,X1) | k1_xboole_0 = X1) ) | ~spl7_1),
% 0.22/0.58    inference(superposition,[],[f40,f158])).
% 0.22/0.58  fof(f158,plain,(
% 0.22/0.58    sK1 = k4_tarski(sK1,sK3) | ~spl7_1),
% 0.22/0.58    inference(forward_demodulation,[],[f35,f154])).
% 0.22/0.58  fof(f154,plain,(
% 0.22/0.58    sK1 = sK2 | ~spl7_1),
% 0.22/0.58    inference(backward_demodulation,[],[f82,f73])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    sK1 = k1_mcart_1(sK1) | ~spl7_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f71])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    spl7_1 <=> sK1 = k1_mcart_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    k1_mcart_1(sK1) = sK2),
% 0.22/0.58    inference(superposition,[],[f42,f35])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    sK1 = k4_tarski(sK2,sK3)),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    (sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & sK1 = k4_tarski(sK2,sK3)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f20,f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & ? [X2,X1] : k4_tarski(X1,X2) = sK1)),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ? [X2,X1] : k4_tarski(X1,X2) = sK1 => sK1 = k4_tarski(sK2,sK3)),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.58    inference(negated_conjecture,[],[f10])).
% 0.22/0.58  fof(f10,conjecture,(
% 0.22/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 0.22/0.58    inference(resolution,[],[f67,f69])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ( ! [X0,X1] : (sP0(X1,X0,k2_tarski(X0,X1))) )),
% 0.22/0.58    inference(equality_resolution,[],[f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.58    inference(nnf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.58    inference(definition_folding,[],[f2,f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.58    inference(equality_resolution,[],[f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.58    inference(rectify,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.58    inference(flattening,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.58    inference(nnf_transformation,[],[f17])).
% 0.22/0.58  fof(f153,plain,(
% 0.22/0.58    ~spl7_2),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f152])).
% 0.22/0.58  fof(f152,plain,(
% 0.22/0.58    $false | ~spl7_2),
% 0.22/0.58    inference(subsumption_resolution,[],[f146,f90])).
% 0.22/0.58  fof(f146,plain,(
% 0.22/0.58    r2_hidden(sK1,k1_xboole_0) | ~spl7_2),
% 0.22/0.58    inference(superposition,[],[f92,f136])).
% 0.22/0.58  fof(f136,plain,(
% 0.22/0.58    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl7_2),
% 0.22/0.58    inference(resolution,[],[f135,f65])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl7_2),
% 0.22/0.58    inference(subsumption_resolution,[],[f134,f66])).
% 0.22/0.58  fof(f134,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl7_2),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f133])).
% 0.22/0.58  fof(f133,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0 | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl7_2),
% 0.22/0.58    inference(superposition,[],[f128,f97])).
% 0.22/0.58  fof(f128,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != sK4(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl7_2),
% 0.22/0.58    inference(superposition,[],[f41,f85])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    sK1 = k4_tarski(sK2,sK1) | ~spl7_2),
% 0.22/0.58    inference(backward_demodulation,[],[f35,f84])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    sK1 = sK3 | ~spl7_2),
% 0.22/0.58    inference(forward_demodulation,[],[f83,f77])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    sK1 = k2_mcart_1(sK1) | ~spl7_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f75])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    spl7_2 <=> sK1 = k2_mcart_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    k2_mcart_1(sK1) = sK3),
% 0.22/0.58    inference(superposition,[],[f43,f35])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f8])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    spl7_1 | spl7_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f36,f75,f71])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (22920)------------------------------
% 0.22/0.58  % (22920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (22920)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (22920)Memory used [KB]: 10746
% 0.22/0.58  % (22920)Time elapsed: 0.134 s
% 0.22/0.58  % (22920)------------------------------
% 0.22/0.58  % (22920)------------------------------
% 0.22/0.58  % (22913)Success in time 0.21 s
%------------------------------------------------------------------------------
