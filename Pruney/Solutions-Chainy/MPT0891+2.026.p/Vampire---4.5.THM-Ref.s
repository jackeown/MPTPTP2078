%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  152 (1522 expanded)
%              Number of leaves         :   23 ( 530 expanded)
%              Depth                    :   22
%              Number of atoms          :  512 (8355 expanded)
%              Number of equality atoms :  311 (6653 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f692,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f500,f515,f539,f552,f572,f669,f691])).

fof(f691,plain,
    ( ~ spl7_1
    | spl7_15
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f690])).

fof(f690,plain,
    ( $false
    | ~ spl7_1
    | spl7_15
    | spl7_19 ),
    inference(subsumption_resolution,[],[f689,f431])).

fof(f431,plain,
    ( k1_xboole_0 != k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl7_15
  <=> k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f689,plain,
    ( k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | ~ spl7_1
    | spl7_15
    | spl7_19 ),
    inference(subsumption_resolution,[],[f684,f97])).

fof(f97,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f78,f77])).

fof(f77,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f78,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f684,plain,
    ( ~ r2_hidden(k1_mcart_1(sK4),k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | ~ spl7_1
    | spl7_15
    | spl7_19 ),
    inference(trivial_inequality_removal,[],[f683])).

fof(f683,plain,
    ( sK4 != sK4
    | ~ r2_hidden(k1_mcart_1(sK4),k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | ~ spl7_1
    | spl7_15
    | spl7_19 ),
    inference(superposition,[],[f315,f673])).

fof(f673,plain,
    ( sK4 = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | spl7_15
    | spl7_19 ),
    inference(subsumption_resolution,[],[f672,f431])).

fof(f672,plain,
    ( sK4 = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | spl7_19 ),
    inference(trivial_inequality_removal,[],[f670])).

fof(f670,plain,
    ( k1_mcart_1(sK4) != k1_mcart_1(sK4)
    | sK4 = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | spl7_19 ),
    inference(superposition,[],[f498,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( sK5(k1_enumset1(X0,X0,X1)) = X1
      | sK5(k1_enumset1(X0,X0,X1)) = X0
      | k1_enumset1(X0,X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f104,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f53,f78])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f498,plain,
    ( k1_mcart_1(sK4) != sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl7_19
  <=> k1_mcart_1(sK4) = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f315,plain,
    ( ! [X0] :
        ( sK4 != sK5(X0)
        | ~ r2_hidden(k1_mcart_1(sK4),X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_1 ),
    inference(superposition,[],[f42,f307])).

fof(f307,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f299,f302])).

fof(f302,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl7_1 ),
    inference(superposition,[],[f46,f299])).

fof(f46,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f299,plain,
    ( sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f298,f295])).

fof(f295,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f180,f82])).

fof(f82,plain,
    ( sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_1
  <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f180,plain,(
    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f179,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
            | k6_mcart_1(sK1,sK2,sK3,X3) = X3
            | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
          | k6_mcart_1(sK1,sK2,sK3,X3) = X3
          | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
   => ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f179,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f178,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f178,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f174,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f174,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f37,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f52])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f298,plain,(
    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f290,f171])).

fof(f171,plain,(
    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f170,f34])).

fof(f170,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f169,f35])).

fof(f169,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f165,f36])).

fof(f165,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f70,f65])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f52])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f290,plain,(
    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f190,f180])).

fof(f190,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f189,f158])).

fof(f158,plain,(
    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f157,f34])).

fof(f157,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f156,f35])).

fof(f156,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f152,f36])).

fof(f152,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f69,f65])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f52])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f189,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f188,f34])).

fof(f188,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f187,f35])).

fof(f187,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f183,f36])).

fof(f183,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f68,f65])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f51,f52])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f669,plain,
    ( ~ spl7_1
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f668])).

fof(f668,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f667,f98])).

fof(f98,plain,(
    ! [X2,X3] : r2_hidden(X2,k1_enumset1(X3,X3,X2)) ),
    inference(resolution,[],[f78,f76])).

fof(f76,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f667,plain,
    ( ~ r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | ~ spl7_1
    | ~ spl7_20 ),
    inference(trivial_inequality_removal,[],[f666])).

fof(f666,plain,
    ( k1_mcart_1(sK4) != k1_mcart_1(sK4)
    | ~ r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | ~ spl7_1
    | ~ spl7_20 ),
    inference(superposition,[],[f514,f302])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k1_mcart_1(sK4)
        | ~ r2_hidden(X0,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl7_20
  <=> ! [X1,X0] :
        ( k4_tarski(X0,X1) != k1_mcart_1(sK4)
        | ~ r2_hidden(X0,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f572,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f570,f99])).

fof(f99,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f72,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f570,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),sK4)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f298,f291])).

fof(f291,plain,
    ( sK4 = k2_mcart_1(sK4)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f158,f90])).

fof(f90,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_3
  <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f552,plain,(
    ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f544,f94])).

fof(f94,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f44,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f544,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_15 ),
    inference(superposition,[],[f98,f432])).

fof(f432,plain,
    ( k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f430])).

fof(f539,plain,
    ( ~ spl7_2
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f531,f94])).

fof(f531,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(superposition,[],[f98,f525])).

fof(f525,plain,
    ( k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f510,f98])).

fof(f510,plain,
    ( ~ r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(trivial_inequality_removal,[],[f508])).

fof(f508,plain,
    ( k1_mcart_1(sK4) != k1_mcart_1(sK4)
    | ~ r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(superposition,[],[f202,f499])).

fof(f499,plain,
    ( k1_mcart_1(sK4) = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f497])).

fof(f202,plain,
    ( ! [X1] :
        ( k1_mcart_1(sK4) != sK5(X1)
        | ~ r2_hidden(sK4,X1)
        | k1_xboole_0 = X1 )
    | ~ spl7_2 ),
    inference(superposition,[],[f43,f195])).

fof(f195,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4)
    | ~ spl7_2 ),
    inference(superposition,[],[f46,f192])).

fof(f192,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f191,f180])).

fof(f191,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f190,f86])).

fof(f86,plain,
    ( sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_2
  <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f515,plain,
    ( spl7_15
    | spl7_20
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f504,f497,f513,f430])).

fof(f504,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k1_mcart_1(sK4)
        | ~ r2_hidden(X0,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
        | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) )
    | ~ spl7_19 ),
    inference(superposition,[],[f42,f499])).

fof(f500,plain,
    ( spl7_19
    | spl7_15
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f495,f84,f430,f497])).

fof(f495,plain,
    ( k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)
    | k1_mcart_1(sK4) = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))
    | ~ spl7_2 ),
    inference(resolution,[],[f277,f97])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK4),k1_enumset1(X0,X0,sK4))
        | k1_xboole_0 = k1_enumset1(X0,X0,sK4)
        | sK5(k1_enumset1(X0,X0,sK4)) = X0 )
    | ~ spl7_2 ),
    inference(equality_resolution,[],[f224])).

fof(f224,plain,
    ( ! [X2,X3] :
        ( sK4 != X3
        | ~ r2_hidden(k1_mcart_1(sK4),k1_enumset1(X2,X2,X3))
        | k1_xboole_0 = k1_enumset1(X2,X2,X3)
        | sK5(k1_enumset1(X2,X2,X3)) = X2 )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( ! [X2,X3] :
        ( sK4 != X3
        | ~ r2_hidden(k1_mcart_1(sK4),k1_enumset1(X2,X2,X3))
        | k1_xboole_0 = k1_enumset1(X2,X2,X3)
        | sK5(k1_enumset1(X2,X2,X3)) = X2
        | k1_xboole_0 = k1_enumset1(X2,X2,X3) )
    | ~ spl7_2 ),
    inference(superposition,[],[f208,f105])).

fof(f208,plain,
    ( ! [X0] :
        ( sK4 != sK5(X0)
        | ~ r2_hidden(k1_mcart_1(sK4),X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_2 ),
    inference(superposition,[],[f42,f200])).

fof(f200,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f192,f195])).

fof(f91,plain,
    ( spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f38,f88,f84,f80])).

fof(f38,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:55:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (24480)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (24490)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (24490)Refutation not found, incomplete strategy% (24490)------------------------------
% 0.21/0.51  % (24490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24490)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24490)Memory used [KB]: 10618
% 0.21/0.51  % (24490)Time elapsed: 0.105 s
% 0.21/0.51  % (24490)------------------------------
% 0.21/0.51  % (24490)------------------------------
% 0.21/0.51  % (24482)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (24477)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (24508)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (24508)Refutation not found, incomplete strategy% (24508)------------------------------
% 0.21/0.52  % (24508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24508)Memory used [KB]: 1663
% 0.21/0.52  % (24508)Time elapsed: 0.001 s
% 0.21/0.52  % (24508)------------------------------
% 0.21/0.52  % (24508)------------------------------
% 0.21/0.52  % (24491)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (24504)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (24487)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (24484)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (24483)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (24495)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (24495)Refutation not found, incomplete strategy% (24495)------------------------------
% 0.21/0.53  % (24495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24495)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24495)Memory used [KB]: 10618
% 0.21/0.53  % (24495)Time elapsed: 0.127 s
% 0.21/0.53  % (24495)------------------------------
% 0.21/0.53  % (24495)------------------------------
% 0.21/0.53  % (24481)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (24478)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (24478)Refutation not found, incomplete strategy% (24478)------------------------------
% 0.21/0.53  % (24478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24478)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24478)Memory used [KB]: 1663
% 0.21/0.53  % (24478)Time elapsed: 0.125 s
% 0.21/0.53  % (24478)------------------------------
% 0.21/0.53  % (24478)------------------------------
% 0.21/0.53  % (24501)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (24503)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (24507)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (24494)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (24499)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (24485)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (24502)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (24492)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (24506)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (24492)Refutation not found, incomplete strategy% (24492)------------------------------
% 0.21/0.54  % (24492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24498)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (24488)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (24486)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (24489)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (24497)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (24496)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (24492)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24492)Memory used [KB]: 1791
% 0.21/0.55  % (24492)Time elapsed: 0.139 s
% 0.21/0.55  % (24492)------------------------------
% 0.21/0.55  % (24492)------------------------------
% 0.21/0.55  % (24500)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (24496)Refutation not found, incomplete strategy% (24496)------------------------------
% 0.21/0.55  % (24496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24496)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24496)Memory used [KB]: 1791
% 0.21/0.55  % (24496)Time elapsed: 0.139 s
% 0.21/0.55  % (24496)------------------------------
% 0.21/0.55  % (24496)------------------------------
% 0.21/0.55  % (24497)Refutation not found, incomplete strategy% (24497)------------------------------
% 0.21/0.55  % (24497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24497)Memory used [KB]: 1791
% 0.21/0.55  % (24497)Time elapsed: 0.140 s
% 0.21/0.55  % (24497)------------------------------
% 0.21/0.55  % (24497)------------------------------
% 0.21/0.56  % (24507)Refutation not found, incomplete strategy% (24507)------------------------------
% 0.21/0.56  % (24507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24505)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (24503)Refutation not found, incomplete strategy% (24503)------------------------------
% 0.21/0.56  % (24503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24503)Memory used [KB]: 10746
% 0.21/0.56  % (24503)Time elapsed: 0.148 s
% 0.21/0.56  % (24503)------------------------------
% 0.21/0.56  % (24503)------------------------------
% 0.21/0.56  % (24505)Refutation not found, incomplete strategy% (24505)------------------------------
% 0.21/0.56  % (24505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24505)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24505)Memory used [KB]: 6268
% 0.21/0.56  % (24505)Time elapsed: 0.140 s
% 0.21/0.56  % (24505)------------------------------
% 0.21/0.56  % (24505)------------------------------
% 0.21/0.57  % (24506)Refutation not found, incomplete strategy% (24506)------------------------------
% 0.21/0.57  % (24506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24506)Memory used [KB]: 6268
% 0.21/0.57  % (24506)Time elapsed: 0.159 s
% 0.21/0.57  % (24506)------------------------------
% 0.21/0.57  % (24506)------------------------------
% 0.21/0.57  % (24488)Refutation not found, incomplete strategy% (24488)------------------------------
% 0.21/0.57  % (24488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24488)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24488)Memory used [KB]: 11001
% 0.21/0.57  % (24488)Time elapsed: 0.170 s
% 0.21/0.57  % (24488)------------------------------
% 0.21/0.57  % (24488)------------------------------
% 0.21/0.57  % (24507)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24507)Memory used [KB]: 10874
% 0.21/0.57  % (24507)Time elapsed: 0.152 s
% 0.21/0.57  % (24507)------------------------------
% 0.21/0.57  % (24507)------------------------------
% 0.21/0.58  % (24484)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f692,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(avatar_sat_refutation,[],[f91,f500,f515,f539,f552,f572,f669,f691])).
% 1.79/0.60  fof(f691,plain,(
% 1.79/0.60    ~spl7_1 | spl7_15 | spl7_19),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f690])).
% 1.79/0.60  fof(f690,plain,(
% 1.79/0.60    $false | (~spl7_1 | spl7_15 | spl7_19)),
% 1.79/0.60    inference(subsumption_resolution,[],[f689,f431])).
% 1.79/0.60  fof(f431,plain,(
% 1.79/0.60    k1_xboole_0 != k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | spl7_15),
% 1.79/0.60    inference(avatar_component_clause,[],[f430])).
% 1.79/0.60  fof(f430,plain,(
% 1.79/0.60    spl7_15 <=> k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.79/0.60  fof(f689,plain,(
% 1.79/0.60    k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | (~spl7_1 | spl7_15 | spl7_19)),
% 1.79/0.60    inference(subsumption_resolution,[],[f684,f97])).
% 1.79/0.60  fof(f97,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 1.79/0.60    inference(resolution,[],[f78,f77])).
% 1.79/0.60  fof(f77,plain,(
% 1.79/0.60    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.79/0.60    inference(equality_resolution,[],[f54])).
% 1.79/0.60  fof(f54,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f32])).
% 1.79/0.60  fof(f32,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.79/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 1.79/0.60  fof(f31,plain,(
% 1.79/0.60    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f30,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.79/0.60    inference(rectify,[],[f29])).
% 1.79/0.60  fof(f29,plain,(
% 1.79/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.79/0.60    inference(flattening,[],[f28])).
% 1.79/0.60  fof(f28,plain,(
% 1.79/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.79/0.60    inference(nnf_transformation,[],[f19])).
% 1.79/0.60  fof(f19,plain,(
% 1.79/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.79/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.79/0.60  fof(f78,plain,(
% 1.79/0.60    ( ! [X0,X1] : (sP0(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 1.79/0.60    inference(equality_resolution,[],[f67])).
% 1.79/0.60  fof(f67,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.79/0.60    inference(definition_unfolding,[],[f59,f45])).
% 1.79/0.60  fof(f45,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f2])).
% 1.79/0.60  fof(f2,axiom,(
% 1.79/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.79/0.60  fof(f59,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f33])).
% 1.79/0.60  fof(f33,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.79/0.60    inference(nnf_transformation,[],[f20])).
% 1.79/0.60  fof(f20,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.79/0.60    inference(definition_folding,[],[f1,f19])).
% 1.79/0.60  fof(f1,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.79/0.60  fof(f684,plain,(
% 1.79/0.60    ~r2_hidden(k1_mcart_1(sK4),k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | (~spl7_1 | spl7_15 | spl7_19)),
% 1.79/0.60    inference(trivial_inequality_removal,[],[f683])).
% 1.79/0.60  fof(f683,plain,(
% 1.79/0.60    sK4 != sK4 | ~r2_hidden(k1_mcart_1(sK4),k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | (~spl7_1 | spl7_15 | spl7_19)),
% 1.79/0.60    inference(superposition,[],[f315,f673])).
% 1.79/0.60  fof(f673,plain,(
% 1.79/0.60    sK4 = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | (spl7_15 | spl7_19)),
% 1.79/0.60    inference(subsumption_resolution,[],[f672,f431])).
% 1.79/0.60  fof(f672,plain,(
% 1.79/0.60    sK4 = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | spl7_19),
% 1.79/0.60    inference(trivial_inequality_removal,[],[f670])).
% 1.79/0.60  fof(f670,plain,(
% 1.79/0.60    k1_mcart_1(sK4) != k1_mcart_1(sK4) | sK4 = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | spl7_19),
% 1.79/0.60    inference(superposition,[],[f498,f105])).
% 1.79/0.60  fof(f105,plain,(
% 1.79/0.60    ( ! [X0,X1] : (sK5(k1_enumset1(X0,X0,X1)) = X1 | sK5(k1_enumset1(X0,X0,X1)) = X0 | k1_enumset1(X0,X0,X1) = k1_xboole_0) )),
% 1.79/0.60    inference(resolution,[],[f104,f41])).
% 1.79/0.60  fof(f41,plain,(
% 1.79/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f25])).
% 1.79/0.60  fof(f25,plain,(
% 1.79/0.60    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 1.79/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f24])).
% 1.79/0.60  fof(f24,plain,(
% 1.79/0.60    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f16,plain,(
% 1.79/0.60    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.79/0.60    inference(ennf_transformation,[],[f11])).
% 1.79/0.60  fof(f11,axiom,(
% 1.79/0.60    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.79/0.60  fof(f104,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_enumset1(X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.79/0.60    inference(resolution,[],[f53,f78])).
% 1.79/0.60  fof(f53,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.79/0.60    inference(cnf_transformation,[],[f32])).
% 1.79/0.60  fof(f498,plain,(
% 1.79/0.60    k1_mcart_1(sK4) != sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | spl7_19),
% 1.79/0.60    inference(avatar_component_clause,[],[f497])).
% 1.79/0.60  fof(f497,plain,(
% 1.79/0.60    spl7_19 <=> k1_mcart_1(sK4) = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.79/0.60  fof(f315,plain,(
% 1.79/0.60    ( ! [X0] : (sK4 != sK5(X0) | ~r2_hidden(k1_mcart_1(sK4),X0) | k1_xboole_0 = X0) ) | ~spl7_1),
% 1.79/0.60    inference(superposition,[],[f42,f307])).
% 1.79/0.60  fof(f307,plain,(
% 1.79/0.60    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl7_1),
% 1.79/0.60    inference(backward_demodulation,[],[f299,f302])).
% 1.79/0.60  fof(f302,plain,(
% 1.79/0.60    k1_mcart_1(sK4) = k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))) | ~spl7_1),
% 1.79/0.60    inference(superposition,[],[f46,f299])).
% 1.79/0.60  fof(f46,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f10])).
% 1.79/0.60  fof(f10,axiom,(
% 1.79/0.60    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.79/0.60  fof(f299,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) | ~spl7_1),
% 1.79/0.60    inference(forward_demodulation,[],[f298,f295])).
% 1.79/0.60  fof(f295,plain,(
% 1.79/0.60    sK4 = k1_mcart_1(k1_mcart_1(sK4)) | ~spl7_1),
% 1.79/0.60    inference(backward_demodulation,[],[f180,f82])).
% 1.79/0.60  fof(f82,plain,(
% 1.79/0.60    sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_1),
% 1.79/0.60    inference(avatar_component_clause,[],[f80])).
% 1.79/0.60  fof(f80,plain,(
% 1.79/0.60    spl7_1 <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.79/0.60  fof(f180,plain,(
% 1.79/0.60    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 1.79/0.60    inference(subsumption_resolution,[],[f179,f34])).
% 1.79/0.60  fof(f34,plain,(
% 1.79/0.60    k1_xboole_0 != sK1),
% 1.79/0.60    inference(cnf_transformation,[],[f23])).
% 1.79/0.60  fof(f23,plain,(
% 1.79/0.60    ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1),
% 1.79/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f22,f21])).
% 1.79/0.60  fof(f21,plain,(
% 1.79/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1)),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f22,plain,(
% 1.79/0.60    ? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) => ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f14,plain,(
% 1.79/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.79/0.60    inference(ennf_transformation,[],[f13])).
% 1.79/0.60  fof(f13,negated_conjecture,(
% 1.79/0.60    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.79/0.60    inference(negated_conjecture,[],[f12])).
% 1.79/0.60  fof(f12,conjecture,(
% 1.79/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.79/0.60  fof(f179,plain,(
% 1.79/0.60    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f178,f35])).
% 1.79/0.60  fof(f35,plain,(
% 1.79/0.60    k1_xboole_0 != sK2),
% 1.79/0.60    inference(cnf_transformation,[],[f23])).
% 1.79/0.60  fof(f178,plain,(
% 1.79/0.60    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f174,f36])).
% 1.79/0.60  fof(f36,plain,(
% 1.79/0.60    k1_xboole_0 != sK3),
% 1.79/0.60    inference(cnf_transformation,[],[f23])).
% 1.79/0.60  fof(f174,plain,(
% 1.79/0.60    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(resolution,[],[f71,f65])).
% 1.79/0.60  fof(f65,plain,(
% 1.79/0.60    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.79/0.60    inference(definition_unfolding,[],[f37,f52])).
% 1.79/0.60  fof(f52,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f6])).
% 1.79/0.60  fof(f6,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.79/0.60  fof(f37,plain,(
% 1.79/0.60    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.79/0.60    inference(cnf_transformation,[],[f23])).
% 1.79/0.60  fof(f71,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(definition_unfolding,[],[f62,f52])).
% 1.79/0.60  fof(f62,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f18,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.79/0.60    inference(ennf_transformation,[],[f9])).
% 1.79/0.60  fof(f9,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.79/0.60  fof(f298,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))),
% 1.79/0.60    inference(forward_demodulation,[],[f290,f171])).
% 1.79/0.60  fof(f171,plain,(
% 1.79/0.60    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.79/0.60    inference(subsumption_resolution,[],[f170,f34])).
% 1.79/0.60  fof(f170,plain,(
% 1.79/0.60    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f169,f35])).
% 1.79/0.60  fof(f169,plain,(
% 1.79/0.60    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f165,f36])).
% 1.79/0.60  fof(f165,plain,(
% 1.79/0.60    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(resolution,[],[f70,f65])).
% 1.79/0.60  fof(f70,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(definition_unfolding,[],[f63,f52])).
% 1.79/0.60  fof(f63,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f290,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 1.79/0.60    inference(forward_demodulation,[],[f190,f180])).
% 1.79/0.60  fof(f190,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 1.79/0.60    inference(forward_demodulation,[],[f189,f158])).
% 1.79/0.60  fof(f158,plain,(
% 1.79/0.60    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 1.79/0.60    inference(subsumption_resolution,[],[f157,f34])).
% 1.79/0.60  fof(f157,plain,(
% 1.79/0.60    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f156,f35])).
% 1.79/0.60  fof(f156,plain,(
% 1.79/0.60    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f152,f36])).
% 1.79/0.60  fof(f152,plain,(
% 1.79/0.60    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(resolution,[],[f69,f65])).
% 1.79/0.60  fof(f69,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(definition_unfolding,[],[f64,f52])).
% 1.79/0.60  fof(f64,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f189,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))),
% 1.79/0.60    inference(subsumption_resolution,[],[f188,f34])).
% 1.79/0.60  fof(f188,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f187,f35])).
% 1.79/0.60  fof(f187,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(subsumption_resolution,[],[f183,f36])).
% 1.79/0.60  fof(f183,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.79/0.60    inference(resolution,[],[f68,f65])).
% 1.79/0.60  fof(f68,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(definition_unfolding,[],[f61,f51,f52])).
% 1.79/0.60  fof(f51,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f5])).
% 1.79/0.60  fof(f5,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.79/0.60  fof(f61,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f17])).
% 1.79/0.60  fof(f17,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.79/0.60    inference(ennf_transformation,[],[f8])).
% 1.79/0.60  fof(f8,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.79/0.60  fof(f42,plain,(
% 1.79/0.60    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f25])).
% 1.79/0.60  fof(f669,plain,(
% 1.79/0.60    ~spl7_1 | ~spl7_20),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f668])).
% 1.79/0.60  fof(f668,plain,(
% 1.79/0.60    $false | (~spl7_1 | ~spl7_20)),
% 1.79/0.60    inference(subsumption_resolution,[],[f667,f98])).
% 1.79/0.60  fof(f98,plain,(
% 1.79/0.60    ( ! [X2,X3] : (r2_hidden(X2,k1_enumset1(X3,X3,X2))) )),
% 1.79/0.60    inference(resolution,[],[f78,f76])).
% 1.79/0.60  fof(f76,plain,(
% 1.79/0.60    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.79/0.60    inference(equality_resolution,[],[f55])).
% 1.79/0.60  fof(f55,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f32])).
% 1.79/0.60  fof(f667,plain,(
% 1.79/0.60    ~r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | (~spl7_1 | ~spl7_20)),
% 1.79/0.60    inference(trivial_inequality_removal,[],[f666])).
% 1.79/0.60  fof(f666,plain,(
% 1.79/0.60    k1_mcart_1(sK4) != k1_mcart_1(sK4) | ~r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | (~spl7_1 | ~spl7_20)),
% 1.79/0.60    inference(superposition,[],[f514,f302])).
% 1.79/0.60  fof(f514,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k4_tarski(X0,X1) != k1_mcart_1(sK4) | ~r2_hidden(X0,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4))) ) | ~spl7_20),
% 1.79/0.60    inference(avatar_component_clause,[],[f513])).
% 1.79/0.60  fof(f513,plain,(
% 1.79/0.60    spl7_20 <=> ! [X1,X0] : (k4_tarski(X0,X1) != k1_mcart_1(sK4) | ~r2_hidden(X0,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.79/0.60  fof(f572,plain,(
% 1.79/0.60    ~spl7_3),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f571])).
% 1.79/0.60  fof(f571,plain,(
% 1.79/0.60    $false | ~spl7_3),
% 1.79/0.60    inference(subsumption_resolution,[],[f570,f99])).
% 1.79/0.60  fof(f99,plain,(
% 1.79/0.60    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.79/0.60    inference(forward_demodulation,[],[f72,f47])).
% 1.79/0.60  fof(f47,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f10])).
% 1.79/0.60  fof(f72,plain,(
% 1.79/0.60    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.79/0.60    inference(equality_resolution,[],[f40])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f15])).
% 1.79/0.60  fof(f15,plain,(
% 1.79/0.60    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.79/0.60    inference(ennf_transformation,[],[f7])).
% 1.79/0.60  fof(f7,axiom,(
% 1.79/0.60    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.79/0.60  fof(f570,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),sK4) | ~spl7_3),
% 1.79/0.60    inference(forward_demodulation,[],[f298,f291])).
% 1.79/0.60  fof(f291,plain,(
% 1.79/0.60    sK4 = k2_mcart_1(sK4) | ~spl7_3),
% 1.79/0.60    inference(backward_demodulation,[],[f158,f90])).
% 1.79/0.60  fof(f90,plain,(
% 1.79/0.60    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_3),
% 1.79/0.60    inference(avatar_component_clause,[],[f88])).
% 1.79/0.60  fof(f88,plain,(
% 1.79/0.60    spl7_3 <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.79/0.60  fof(f552,plain,(
% 1.79/0.60    ~spl7_15),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f551])).
% 1.79/0.60  fof(f551,plain,(
% 1.79/0.60    $false | ~spl7_15),
% 1.79/0.60    inference(subsumption_resolution,[],[f544,f94])).
% 1.79/0.60  fof(f94,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.79/0.60    inference(superposition,[],[f44,f74])).
% 1.79/0.60  fof(f74,plain,(
% 1.79/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f50])).
% 1.79/0.60  fof(f50,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f27])).
% 1.79/0.60  fof(f27,plain,(
% 1.79/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.79/0.60    inference(flattening,[],[f26])).
% 1.79/0.60  fof(f26,plain,(
% 1.79/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.79/0.60    inference(nnf_transformation,[],[f3])).
% 1.79/0.60  fof(f3,axiom,(
% 1.79/0.60    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.79/0.60  fof(f44,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f4])).
% 1.79/0.60  fof(f4,axiom,(
% 1.79/0.60    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.79/0.60  fof(f544,plain,(
% 1.79/0.60    r2_hidden(sK4,k1_xboole_0) | ~spl7_15),
% 1.79/0.60    inference(superposition,[],[f98,f432])).
% 1.79/0.60  fof(f432,plain,(
% 1.79/0.60    k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | ~spl7_15),
% 1.79/0.60    inference(avatar_component_clause,[],[f430])).
% 1.79/0.60  fof(f539,plain,(
% 1.79/0.60    ~spl7_2 | ~spl7_19),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f538])).
% 1.79/0.60  fof(f538,plain,(
% 1.79/0.60    $false | (~spl7_2 | ~spl7_19)),
% 1.79/0.60    inference(subsumption_resolution,[],[f531,f94])).
% 1.79/0.60  fof(f531,plain,(
% 1.79/0.60    r2_hidden(sK4,k1_xboole_0) | (~spl7_2 | ~spl7_19)),
% 1.79/0.60    inference(superposition,[],[f98,f525])).
% 1.79/0.60  fof(f525,plain,(
% 1.79/0.60    k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | (~spl7_2 | ~spl7_19)),
% 1.79/0.60    inference(subsumption_resolution,[],[f510,f98])).
% 1.79/0.60  fof(f510,plain,(
% 1.79/0.60    ~r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | (~spl7_2 | ~spl7_19)),
% 1.79/0.60    inference(trivial_inequality_removal,[],[f508])).
% 1.79/0.60  fof(f508,plain,(
% 1.79/0.60    k1_mcart_1(sK4) != k1_mcart_1(sK4) | ~r2_hidden(sK4,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | (~spl7_2 | ~spl7_19)),
% 1.79/0.60    inference(superposition,[],[f202,f499])).
% 1.79/0.60  fof(f499,plain,(
% 1.79/0.60    k1_mcart_1(sK4) = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | ~spl7_19),
% 1.79/0.60    inference(avatar_component_clause,[],[f497])).
% 1.79/0.60  fof(f202,plain,(
% 1.79/0.60    ( ! [X1] : (k1_mcart_1(sK4) != sK5(X1) | ~r2_hidden(sK4,X1) | k1_xboole_0 = X1) ) | ~spl7_2),
% 1.79/0.60    inference(superposition,[],[f43,f195])).
% 1.79/0.60  fof(f195,plain,(
% 1.79/0.60    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4) | ~spl7_2),
% 1.79/0.60    inference(superposition,[],[f46,f192])).
% 1.79/0.60  fof(f192,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4)) | ~spl7_2),
% 1.79/0.60    inference(forward_demodulation,[],[f191,f180])).
% 1.79/0.60  fof(f191,plain,(
% 1.79/0.60    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4)) | ~spl7_2),
% 1.79/0.60    inference(forward_demodulation,[],[f190,f86])).
% 1.79/0.60  fof(f86,plain,(
% 1.79/0.60    sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_2),
% 1.79/0.60    inference(avatar_component_clause,[],[f84])).
% 1.79/0.60  fof(f84,plain,(
% 1.79/0.60    spl7_2 <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.79/0.60  fof(f43,plain,(
% 1.79/0.60    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f25])).
% 1.79/0.60  fof(f515,plain,(
% 1.79/0.60    spl7_15 | spl7_20 | ~spl7_19),
% 1.79/0.60    inference(avatar_split_clause,[],[f504,f497,f513,f430])).
% 1.79/0.60  fof(f504,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k4_tarski(X0,X1) != k1_mcart_1(sK4) | ~r2_hidden(X0,k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) ) | ~spl7_19),
% 1.79/0.60    inference(superposition,[],[f42,f499])).
% 1.79/0.60  fof(f500,plain,(
% 1.79/0.60    spl7_19 | spl7_15 | ~spl7_2),
% 1.79/0.60    inference(avatar_split_clause,[],[f495,f84,f430,f497])).
% 1.79/0.60  fof(f495,plain,(
% 1.79/0.60    k1_xboole_0 = k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4) | k1_mcart_1(sK4) = sK5(k1_enumset1(k1_mcart_1(sK4),k1_mcart_1(sK4),sK4)) | ~spl7_2),
% 1.79/0.60    inference(resolution,[],[f277,f97])).
% 1.79/0.60  fof(f277,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k1_enumset1(X0,X0,sK4)) | k1_xboole_0 = k1_enumset1(X0,X0,sK4) | sK5(k1_enumset1(X0,X0,sK4)) = X0) ) | ~spl7_2),
% 1.79/0.60    inference(equality_resolution,[],[f224])).
% 1.79/0.60  fof(f224,plain,(
% 1.79/0.60    ( ! [X2,X3] : (sK4 != X3 | ~r2_hidden(k1_mcart_1(sK4),k1_enumset1(X2,X2,X3)) | k1_xboole_0 = k1_enumset1(X2,X2,X3) | sK5(k1_enumset1(X2,X2,X3)) = X2) ) | ~spl7_2),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f221])).
% 1.79/0.60  fof(f221,plain,(
% 1.79/0.60    ( ! [X2,X3] : (sK4 != X3 | ~r2_hidden(k1_mcart_1(sK4),k1_enumset1(X2,X2,X3)) | k1_xboole_0 = k1_enumset1(X2,X2,X3) | sK5(k1_enumset1(X2,X2,X3)) = X2 | k1_xboole_0 = k1_enumset1(X2,X2,X3)) ) | ~spl7_2),
% 1.79/0.60    inference(superposition,[],[f208,f105])).
% 1.79/0.60  fof(f208,plain,(
% 1.79/0.60    ( ! [X0] : (sK4 != sK5(X0) | ~r2_hidden(k1_mcart_1(sK4),X0) | k1_xboole_0 = X0) ) | ~spl7_2),
% 1.79/0.60    inference(superposition,[],[f42,f200])).
% 1.79/0.60  fof(f200,plain,(
% 1.79/0.60    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl7_2),
% 1.79/0.60    inference(backward_demodulation,[],[f192,f195])).
% 1.79/0.60  fof(f91,plain,(
% 1.79/0.60    spl7_1 | spl7_2 | spl7_3),
% 1.79/0.60    inference(avatar_split_clause,[],[f38,f88,f84,f80])).
% 1.79/0.60  fof(f38,plain,(
% 1.79/0.60    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.79/0.60    inference(cnf_transformation,[],[f23])).
% 1.79/0.60  % SZS output end Proof for theBenchmark
% 1.79/0.60  % (24484)------------------------------
% 1.79/0.60  % (24484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (24484)Termination reason: Refutation
% 1.79/0.60  
% 1.79/0.60  % (24484)Memory used [KB]: 11001
% 1.79/0.60  % (24484)Time elapsed: 0.126 s
% 1.79/0.60  % (24484)------------------------------
% 1.79/0.60  % (24484)------------------------------
% 1.79/0.60  % (24475)Success in time 0.234 s
%------------------------------------------------------------------------------
