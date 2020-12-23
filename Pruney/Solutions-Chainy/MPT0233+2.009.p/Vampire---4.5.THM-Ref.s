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
% DateTime   : Thu Dec  3 12:37:05 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  172 (1876 expanded)
%              Number of leaves         :   27 ( 588 expanded)
%              Depth                    :   28
%              Number of atoms          :  461 (4552 expanded)
%              Number of equality atoms :  294 (3595 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f530,f617,f1418,f1450,f1544])).

fof(f1544,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1543])).

fof(f1543,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1539,f1497])).

fof(f1497,plain,
    ( sK0 != sK1
    | ~ spl5_3 ),
    inference(superposition,[],[f44,f1479])).

fof(f1479,plain,
    ( sK1 = sK2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1478,f44])).

fof(f1478,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f1477])).

fof(f1477,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl5_3 ),
    inference(resolution,[],[f1457,f118])).

fof(f118,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f70,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1457,plain,
    ( r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_3 ),
    inference(superposition,[],[f113,f132])).

fof(f132,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f113,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f44,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f1539,plain,
    ( sK0 = sK1
    | ~ spl5_3 ),
    inference(resolution,[],[f1494,f117])).

fof(f117,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f71,f85])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1494,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X2 )
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f1471,f1479])).

fof(f1471,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK2 = X2 )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f1460])).

fof(f1460,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK2 = X2
        | sK2 = X2
        | sK2 = X2 )
    | ~ spl5_3 ),
    inference(superposition,[],[f118,f132])).

fof(f1450,plain,
    ( spl5_2
    | spl5_3
    | spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1449,f134,f122,f130,f126])).

fof(f126,plain,
    ( spl5_2
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f122,plain,
    ( spl5_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f134,plain,
    ( spl5_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1449,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f1448,f123])).

fof(f123,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1448,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f531,f135])).

fof(f135,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f531,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(resolution,[],[f89,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f62,f86,f87,f87,f86])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f86])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f85])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f89,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f43,f86,f86])).

fof(f43,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1418,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1417])).

fof(f1417,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1416,f45])).

fof(f45,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f1416,plain,
    ( sK0 = sK3
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1412,f44])).

fof(f1412,plain,
    ( sK0 = sK2
    | sK0 = sK3
    | ~ spl5_2 ),
    inference(resolution,[],[f1349,f117])).

fof(f1349,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK3))
        | sK2 = X2
        | sK3 = X2 )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f1334,f1340])).

fof(f1340,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK3)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1339,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f58,f85,f85])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f1339,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1338,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f59,f85,f85])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(f1338,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1337,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1337,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3),k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1336,f46])).

fof(f1336,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1325,f1280])).

fof(f1280,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f624,f1277])).

fof(f1277,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f673,f1276])).

fof(f1276,plain,
    ( k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1268,f46])).

fof(f1268,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3)
    | ~ spl5_2 ),
    inference(superposition,[],[f719,f624])).

fof(f719,plain,
    ( ! [X8,X7,X9] : k6_enumset1(sK0,sK0,sK0,sK0,sK0,X7,X8,X9) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k1_xboole_0,k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f711,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f711,plain,
    ( ! [X8,X7,X9] : k6_enumset1(sK0,sK0,sK0,sK0,sK0,X7,X8,X9) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k1_xboole_0)))
    | ~ spl5_2 ),
    inference(superposition,[],[f98,f691])).

fof(f691,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f636,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f636,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f110,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f110,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f64,f86,f87])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f68,f84,f81,f87,f85])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f673,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f672,f46])).

fof(f672,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f671,f624])).

fof(f671,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f670,f52])).

fof(f670,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f669,f46])).

fof(f669,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f665,f46])).

fof(f665,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl5_2 ),
    inference(superposition,[],[f90,f624])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f81,f81])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f624,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f120,f128])).

fof(f120,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f89,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1325,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3))))
    | ~ spl5_2 ),
    inference(superposition,[],[f710,f1277])).

fof(f710,plain,
    ( ! [X6,X4,X5] : k6_enumset1(X4,X4,X4,X4,X4,X5,X6,sK0) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6))))
    | ~ spl5_2 ),
    inference(superposition,[],[f99,f691])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f69,f84,f81,f85,f87])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f1334,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3))
        | sK2 = X2
        | sK3 = X2 )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f1324])).

fof(f1324,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3))
        | sK2 = X2
        | sK2 = X2
        | sK3 = X2 )
    | ~ spl5_2 ),
    inference(superposition,[],[f118,f1277])).

fof(f617,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f612,f576])).

fof(f576,plain,
    ( sK0 != sK1
    | ~ spl5_4 ),
    inference(superposition,[],[f45,f556])).

fof(f556,plain,
    ( sK1 = sK3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f555,f45])).

fof(f555,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f554])).

fof(f554,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl5_4 ),
    inference(resolution,[],[f536,f118])).

fof(f536,plain,
    ( r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f113,f136])).

fof(f136,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f612,plain,
    ( sK0 = sK1
    | ~ spl5_4 ),
    inference(resolution,[],[f571,f117])).

fof(f571,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X2 )
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f550,f556])).

fof(f550,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK3 = X2 )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f539])).

fof(f539,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK3 = X2
        | sK3 = X2
        | sK3 = X2 )
    | ~ spl5_4 ),
    inference(superposition,[],[f118,f136])).

fof(f530,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f528,f498])).

fof(f498,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f456,f480])).

fof(f480,plain,
    ( sK1 = sK2
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f479,f44])).

fof(f479,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f478])).

fof(f478,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl5_1 ),
    inference(resolution,[],[f403,f118])).

fof(f403,plain,
    ( r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f115,f124])).

fof(f124,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f115,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f85])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f456,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1,sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f440,f91])).

fof(f440,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f124,f439])).

fof(f439,plain,
    ( sK1 = sK3
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f438,f45])).

fof(f438,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f437])).

fof(f437,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl5_1 ),
    inference(resolution,[],[f402,f118])).

fof(f402,plain,
    ( r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f113,f124])).

fof(f528,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_1
    | spl5_3 ),
    inference(forward_demodulation,[],[f131,f480])).

fof(f131,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (20851)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (20858)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (20851)Refutation not found, incomplete strategy% (20851)------------------------------
% 0.21/0.52  % (20851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20851)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20851)Memory used [KB]: 1663
% 0.21/0.52  % (20851)Time elapsed: 0.077 s
% 0.21/0.52  % (20851)------------------------------
% 0.21/0.52  % (20851)------------------------------
% 0.21/0.57  % (20852)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (20856)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (20863)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (20876)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (20874)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (20853)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (20867)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (20854)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (20865)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (20873)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (20855)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (20875)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.59  % (20871)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.68/0.59  % (20866)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.68/0.59  % (20868)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.68/0.59  % (20866)Refutation not found, incomplete strategy% (20866)------------------------------
% 1.68/0.59  % (20866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (20866)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (20866)Memory used [KB]: 6268
% 1.68/0.59  % (20866)Time elapsed: 0.120 s
% 1.68/0.59  % (20866)------------------------------
% 1.68/0.59  % (20866)------------------------------
% 1.68/0.59  % (20860)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.59  % (20860)Refutation not found, incomplete strategy% (20860)------------------------------
% 1.68/0.59  % (20860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (20860)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (20860)Memory used [KB]: 10618
% 1.68/0.59  % (20860)Time elapsed: 0.176 s
% 1.68/0.59  % (20860)------------------------------
% 1.68/0.59  % (20860)------------------------------
% 1.68/0.59  % (20864)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.68/0.60  % (20870)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.68/0.60  % (20857)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.68/0.60  % (20880)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.68/0.60  % (20878)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.68/0.60  % (20869)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.68/0.61  % (20862)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.92/0.61  % (20859)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.92/0.61  % (20872)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.92/0.62  % (20879)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.92/0.62  % (20861)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.92/0.62  % (20877)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.92/0.64  % (20905)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.92/0.64  % (20861)Refutation not found, incomplete strategy% (20861)------------------------------
% 1.92/0.64  % (20861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.64  % (20861)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.64  
% 1.92/0.64  % (20861)Memory used [KB]: 10618
% 1.92/0.64  % (20861)Time elapsed: 0.216 s
% 1.92/0.64  % (20861)------------------------------
% 1.92/0.64  % (20861)------------------------------
% 2.82/0.76  % (20909)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.82/0.78  % (20908)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.22/0.81  % (20859)Refutation found. Thanks to Tanya!
% 3.22/0.81  % SZS status Theorem for theBenchmark
% 3.22/0.81  % SZS output start Proof for theBenchmark
% 3.22/0.81  fof(f1545,plain,(
% 3.22/0.81    $false),
% 3.22/0.81    inference(avatar_sat_refutation,[],[f530,f617,f1418,f1450,f1544])).
% 3.22/0.81  fof(f1544,plain,(
% 3.22/0.81    ~spl5_3),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f1543])).
% 3.22/0.81  fof(f1543,plain,(
% 3.22/0.81    $false | ~spl5_3),
% 3.22/0.81    inference(subsumption_resolution,[],[f1539,f1497])).
% 3.22/0.81  fof(f1497,plain,(
% 3.22/0.81    sK0 != sK1 | ~spl5_3),
% 3.22/0.81    inference(superposition,[],[f44,f1479])).
% 3.22/0.81  fof(f1479,plain,(
% 3.22/0.81    sK1 = sK2 | ~spl5_3),
% 3.22/0.81    inference(subsumption_resolution,[],[f1478,f44])).
% 3.22/0.81  fof(f1478,plain,(
% 3.22/0.81    sK0 = sK2 | sK1 = sK2 | ~spl5_3),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f1477])).
% 3.22/0.81  fof(f1477,plain,(
% 3.22/0.81    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl5_3),
% 3.22/0.81    inference(resolution,[],[f1457,f118])).
% 3.22/0.81  fof(f118,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 3.22/0.81    inference(equality_resolution,[],[f107])).
% 3.22/0.81  fof(f107,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.22/0.81    inference(definition_unfolding,[],[f70,f85])).
% 3.22/0.81  fof(f85,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f60,f84])).
% 3.22/0.81  fof(f84,plain,(
% 3.22/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f67,f83])).
% 3.22/0.81  fof(f83,plain,(
% 3.22/0.81    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f78,f82])).
% 3.22/0.81  fof(f82,plain,(
% 3.22/0.81    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f79,f80])).
% 3.22/0.81  fof(f80,plain,(
% 3.22/0.81    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f22])).
% 3.22/0.81  fof(f22,axiom,(
% 3.22/0.81    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 3.22/0.81  fof(f79,plain,(
% 3.22/0.81    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f21])).
% 3.22/0.81  fof(f21,axiom,(
% 3.22/0.81    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 3.22/0.81  fof(f78,plain,(
% 3.22/0.81    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f20])).
% 3.22/0.81  fof(f20,axiom,(
% 3.22/0.81    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.22/0.81  fof(f67,plain,(
% 3.22/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f19])).
% 3.22/0.81  fof(f19,axiom,(
% 3.22/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.22/0.81  fof(f60,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f18])).
% 3.22/0.81  fof(f18,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.22/0.81  fof(f70,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.22/0.81    inference(cnf_transformation,[],[f42])).
% 3.22/0.81  fof(f42,plain,(
% 3.22/0.81    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 3.22/0.81  fof(f41,plain,(
% 3.22/0.81    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f40,plain,(
% 3.22/0.81    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.22/0.81    inference(rectify,[],[f39])).
% 3.22/0.81  fof(f39,plain,(
% 3.22/0.81    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.22/0.81    inference(flattening,[],[f38])).
% 3.22/0.81  fof(f38,plain,(
% 3.22/0.81    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.22/0.81    inference(nnf_transformation,[],[f33])).
% 3.22/0.81  fof(f33,plain,(
% 3.22/0.81    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.22/0.81    inference(ennf_transformation,[],[f12])).
% 3.22/0.81  fof(f12,axiom,(
% 3.22/0.81    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 3.22/0.81  fof(f1457,plain,(
% 3.22/0.81    r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_3),
% 3.22/0.81    inference(superposition,[],[f113,f132])).
% 3.22/0.81  fof(f132,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl5_3),
% 3.22/0.81    inference(avatar_component_clause,[],[f130])).
% 3.22/0.81  fof(f130,plain,(
% 3.22/0.81    spl5_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.22/0.81  fof(f113,plain,(
% 3.22/0.81    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 3.22/0.81    inference(equality_resolution,[],[f112])).
% 3.22/0.81  fof(f112,plain,(
% 3.22/0.81    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.22/0.81    inference(equality_resolution,[],[f104])).
% 3.22/0.81  fof(f104,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.22/0.81    inference(definition_unfolding,[],[f73,f85])).
% 3.22/0.81  fof(f73,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.22/0.81    inference(cnf_transformation,[],[f42])).
% 3.22/0.81  fof(f44,plain,(
% 3.22/0.81    sK0 != sK2),
% 3.22/0.81    inference(cnf_transformation,[],[f35])).
% 3.22/0.81  fof(f35,plain,(
% 3.22/0.81    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 3.22/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f34])).
% 3.22/0.81  fof(f34,plain,(
% 3.22/0.81    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 3.22/0.81    introduced(choice_axiom,[])).
% 3.22/0.81  fof(f28,plain,(
% 3.22/0.81    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.22/0.81    inference(ennf_transformation,[],[f26])).
% 3.22/0.81  fof(f26,negated_conjecture,(
% 3.22/0.81    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.22/0.81    inference(negated_conjecture,[],[f25])).
% 3.22/0.81  fof(f25,conjecture,(
% 3.22/0.81    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 3.22/0.81  fof(f1539,plain,(
% 3.22/0.81    sK0 = sK1 | ~spl5_3),
% 3.22/0.81    inference(resolution,[],[f1494,f117])).
% 3.22/0.81  fof(f117,plain,(
% 3.22/0.81    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 3.22/0.81    inference(equality_resolution,[],[f116])).
% 3.22/0.81  fof(f116,plain,(
% 3.22/0.81    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.22/0.81    inference(equality_resolution,[],[f106])).
% 3.22/0.81  fof(f106,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.22/0.81    inference(definition_unfolding,[],[f71,f85])).
% 3.22/0.81  fof(f71,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.22/0.81    inference(cnf_transformation,[],[f42])).
% 3.22/0.81  fof(f1494,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X2) ) | ~spl5_3),
% 3.22/0.81    inference(backward_demodulation,[],[f1471,f1479])).
% 3.22/0.81  fof(f1471,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 = X2) ) | ~spl5_3),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f1460])).
% 3.22/0.81  fof(f1460,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 = X2 | sK2 = X2 | sK2 = X2) ) | ~spl5_3),
% 3.22/0.81    inference(superposition,[],[f118,f132])).
% 3.22/0.81  fof(f1450,plain,(
% 3.22/0.81    spl5_2 | spl5_3 | spl5_1 | spl5_4),
% 3.22/0.81    inference(avatar_split_clause,[],[f1449,f134,f122,f130,f126])).
% 3.22/0.81  fof(f126,plain,(
% 3.22/0.81    spl5_2 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.22/0.81  fof(f122,plain,(
% 3.22/0.81    spl5_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.22/0.81  fof(f134,plain,(
% 3.22/0.81    spl5_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.22/0.81  fof(f1449,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | (spl5_1 | spl5_4)),
% 3.22/0.81    inference(subsumption_resolution,[],[f1448,f123])).
% 3.22/0.81  fof(f123,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) | spl5_1),
% 3.22/0.81    inference(avatar_component_clause,[],[f122])).
% 3.22/0.81  fof(f1448,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) | spl5_4),
% 3.22/0.81    inference(subsumption_resolution,[],[f531,f135])).
% 3.22/0.81  fof(f135,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | spl5_4),
% 3.22/0.81    inference(avatar_component_clause,[],[f134])).
% 3.22/0.81  fof(f531,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 3.22/0.81    inference(resolution,[],[f89,f97])).
% 3.22/0.81  fof(f97,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 3.22/0.81    inference(definition_unfolding,[],[f62,f86,f87,f87,f86])).
% 3.22/0.81  fof(f87,plain,(
% 3.22/0.81    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f47,f86])).
% 3.22/0.81  fof(f47,plain,(
% 3.22/0.81    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f16])).
% 3.22/0.81  fof(f16,axiom,(
% 3.22/0.81    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.22/0.81  fof(f86,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f53,f85])).
% 3.22/0.81  fof(f53,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f17])).
% 3.22/0.81  fof(f17,axiom,(
% 3.22/0.81    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.22/0.81  fof(f62,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f37])).
% 3.22/0.81  fof(f37,plain,(
% 3.22/0.81    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.22/0.81    inference(flattening,[],[f36])).
% 3.22/0.81  fof(f36,plain,(
% 3.22/0.81    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.22/0.81    inference(nnf_transformation,[],[f32])).
% 3.22/0.81  fof(f32,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f24])).
% 3.22/0.81  fof(f24,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 3.22/0.81  fof(f89,plain,(
% 3.22/0.81    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 3.22/0.81    inference(definition_unfolding,[],[f43,f86,f86])).
% 3.22/0.81  fof(f43,plain,(
% 3.22/0.81    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 3.22/0.81    inference(cnf_transformation,[],[f35])).
% 3.22/0.81  fof(f1418,plain,(
% 3.22/0.81    ~spl5_2),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f1417])).
% 3.22/0.81  fof(f1417,plain,(
% 3.22/0.81    $false | ~spl5_2),
% 3.22/0.81    inference(subsumption_resolution,[],[f1416,f45])).
% 3.22/0.81  fof(f45,plain,(
% 3.22/0.81    sK0 != sK3),
% 3.22/0.81    inference(cnf_transformation,[],[f35])).
% 3.22/0.81  fof(f1416,plain,(
% 3.22/0.81    sK0 = sK3 | ~spl5_2),
% 3.22/0.81    inference(subsumption_resolution,[],[f1412,f44])).
% 3.22/0.81  fof(f1412,plain,(
% 3.22/0.81    sK0 = sK2 | sK0 = sK3 | ~spl5_2),
% 3.22/0.81    inference(resolution,[],[f1349,f117])).
% 3.22/0.81  fof(f1349,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK3)) | sK2 = X2 | sK3 = X2) ) | ~spl5_2),
% 3.22/0.81    inference(backward_demodulation,[],[f1334,f1340])).
% 3.22/0.81  fof(f1340,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK3) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f1339,f91])).
% 3.22/0.81  fof(f91,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f58,f85,f85])).
% 3.22/0.81  fof(f58,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f23])).
% 3.22/0.81  fof(f23,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
% 3.22/0.81  fof(f1339,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3,sK2) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f1338,f92])).
% 3.22/0.81  fof(f92,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 3.22/0.81    inference(definition_unfolding,[],[f59,f85,f85])).
% 3.22/0.81  fof(f59,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f13])).
% 3.22/0.81  fof(f13,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).
% 3.22/0.81  fof(f1338,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f1337,f46])).
% 3.22/0.81  fof(f46,plain,(
% 3.22/0.81    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.22/0.81    inference(cnf_transformation,[],[f10])).
% 3.22/0.81  fof(f10,axiom,(
% 3.22/0.81    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 3.22/0.81  fof(f1337,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3),k1_xboole_0) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f1336,f46])).
% 3.22/0.81  fof(f1336,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f1325,f1280])).
% 3.22/0.81  fof(f1280,plain,(
% 3.22/0.81    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3)) | ~spl5_2),
% 3.22/0.81    inference(backward_demodulation,[],[f624,f1277])).
% 3.22/0.81  fof(f1277,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) | ~spl5_2),
% 3.22/0.81    inference(backward_demodulation,[],[f673,f1276])).
% 3.22/0.81  fof(f1276,plain,(
% 3.22/0.81    k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f1268,f46])).
% 3.22/0.81  fof(f1268,plain,(
% 3.22/0.81    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3) | ~spl5_2),
% 3.22/0.81    inference(superposition,[],[f719,f624])).
% 3.22/0.81  fof(f719,plain,(
% 3.22/0.81    ( ! [X8,X7,X9] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,X7,X8,X9) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k1_xboole_0,k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9))))) ) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f711,f52])).
% 3.22/0.81  fof(f52,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f2])).
% 3.22/0.81  fof(f2,axiom,(
% 3.22/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.22/0.81  fof(f711,plain,(
% 3.22/0.81    ( ! [X8,X7,X9] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,X7,X8,X9) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k1_xboole_0)))) ) | ~spl5_2),
% 3.22/0.81    inference(superposition,[],[f98,f691])).
% 3.22/0.81  fof(f691,plain,(
% 3.22/0.81    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_2),
% 3.22/0.81    inference(resolution,[],[f636,f48])).
% 3.22/0.81  fof(f48,plain,(
% 3.22/0.81    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.22/0.81    inference(cnf_transformation,[],[f29])).
% 3.22/0.81  fof(f29,plain,(
% 3.22/0.81    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.22/0.81    inference(ennf_transformation,[],[f8])).
% 3.22/0.81  fof(f8,axiom,(
% 3.22/0.81    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 3.22/0.81  fof(f636,plain,(
% 3.22/0.81    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl5_2),
% 3.22/0.81    inference(superposition,[],[f110,f128])).
% 3.22/0.81  fof(f128,plain,(
% 3.22/0.81    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl5_2),
% 3.22/0.81    inference(avatar_component_clause,[],[f126])).
% 3.22/0.81  fof(f110,plain,(
% 3.22/0.81    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.22/0.81    inference(equality_resolution,[],[f95])).
% 3.22/0.81  fof(f95,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 3.22/0.81    inference(definition_unfolding,[],[f64,f86,f87])).
% 3.22/0.81  fof(f64,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.22/0.81    inference(cnf_transformation,[],[f37])).
% 3.22/0.81  fof(f98,plain,(
% 3.22/0.81    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 3.22/0.81    inference(definition_unfolding,[],[f68,f84,f81,f87,f85])).
% 3.22/0.81  fof(f81,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.22/0.81    inference(definition_unfolding,[],[f55,f54])).
% 3.22/0.81  fof(f54,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f4])).
% 3.22/0.81  fof(f4,axiom,(
% 3.22/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.22/0.81  fof(f55,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f11])).
% 3.22/0.81  fof(f11,axiom,(
% 3.22/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.22/0.81  fof(f68,plain,(
% 3.22/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f14])).
% 3.22/0.81  fof(f14,axiom,(
% 3.22/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 3.22/0.81  fof(f673,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f672,f46])).
% 3.22/0.81  fof(f672,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f671,f624])).
% 3.22/0.81  fof(f671,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f670,f52])).
% 3.22/0.81  fof(f670,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0))) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f669,f46])).
% 3.22/0.81  fof(f669,plain,(
% 3.22/0.81    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0) | ~spl5_2),
% 3.22/0.81    inference(forward_demodulation,[],[f665,f46])).
% 3.22/0.81  fof(f665,plain,(
% 3.22/0.81    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl5_2),
% 3.22/0.81    inference(superposition,[],[f90,f624])).
% 3.22/0.81  fof(f90,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.22/0.81    inference(definition_unfolding,[],[f51,f81,f81])).
% 3.22/0.81  fof(f51,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f1])).
% 3.22/0.81  fof(f1,axiom,(
% 3.22/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.22/0.81  fof(f624,plain,(
% 3.22/0.81    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl5_2),
% 3.22/0.81    inference(backward_demodulation,[],[f120,f128])).
% 3.22/0.81  fof(f120,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 3.22/0.81    inference(resolution,[],[f89,f57])).
% 3.22/0.81  fof(f57,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.22/0.81    inference(cnf_transformation,[],[f30])).
% 3.22/0.81  fof(f30,plain,(
% 3.22/0.81    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.22/0.81    inference(ennf_transformation,[],[f7])).
% 3.22/0.81  fof(f7,axiom,(
% 3.22/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.22/0.81  fof(f1325,plain,(
% 3.22/0.81    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3)))) | ~spl5_2),
% 3.22/0.81    inference(superposition,[],[f710,f1277])).
% 3.22/0.81  fof(f710,plain,(
% 3.22/0.81    ( ! [X6,X4,X5] : (k6_enumset1(X4,X4,X4,X4,X4,X5,X6,sK0) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6))))) ) | ~spl5_2),
% 3.22/0.81    inference(superposition,[],[f99,f691])).
% 3.22/0.81  fof(f99,plain,(
% 3.22/0.81    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))))) )),
% 3.22/0.81    inference(definition_unfolding,[],[f69,f84,f81,f85,f87])).
% 3.22/0.81  fof(f69,plain,(
% 3.22/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f15])).
% 3.22/0.81  fof(f15,axiom,(
% 3.22/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 3.22/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 3.22/0.81  fof(f1334,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3)) | sK2 = X2 | sK3 = X2) ) | ~spl5_2),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f1324])).
% 3.22/0.81  fof(f1324,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2,sK3)) | sK2 = X2 | sK2 = X2 | sK3 = X2) ) | ~spl5_2),
% 3.22/0.81    inference(superposition,[],[f118,f1277])).
% 3.22/0.81  fof(f617,plain,(
% 3.22/0.81    ~spl5_4),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f616])).
% 3.22/0.81  fof(f616,plain,(
% 3.22/0.81    $false | ~spl5_4),
% 3.22/0.81    inference(subsumption_resolution,[],[f612,f576])).
% 3.22/0.81  fof(f576,plain,(
% 3.22/0.81    sK0 != sK1 | ~spl5_4),
% 3.22/0.81    inference(superposition,[],[f45,f556])).
% 3.22/0.81  fof(f556,plain,(
% 3.22/0.81    sK1 = sK3 | ~spl5_4),
% 3.22/0.81    inference(subsumption_resolution,[],[f555,f45])).
% 3.22/0.81  fof(f555,plain,(
% 3.22/0.81    sK0 = sK3 | sK1 = sK3 | ~spl5_4),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f554])).
% 3.22/0.81  fof(f554,plain,(
% 3.22/0.81    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl5_4),
% 3.22/0.81    inference(resolution,[],[f536,f118])).
% 3.22/0.81  fof(f536,plain,(
% 3.22/0.81    r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_4),
% 3.22/0.81    inference(superposition,[],[f113,f136])).
% 3.22/0.81  fof(f136,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl5_4),
% 3.22/0.81    inference(avatar_component_clause,[],[f134])).
% 3.22/0.81  fof(f612,plain,(
% 3.22/0.81    sK0 = sK1 | ~spl5_4),
% 3.22/0.81    inference(resolution,[],[f571,f117])).
% 3.22/0.81  fof(f571,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X2) ) | ~spl5_4),
% 3.22/0.81    inference(backward_demodulation,[],[f550,f556])).
% 3.22/0.81  fof(f550,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK3 = X2) ) | ~spl5_4),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f539])).
% 3.22/0.81  fof(f539,plain,(
% 3.22/0.81    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK3 = X2 | sK3 = X2 | sK3 = X2) ) | ~spl5_4),
% 3.22/0.81    inference(superposition,[],[f118,f136])).
% 3.22/0.81  fof(f530,plain,(
% 3.22/0.81    ~spl5_1 | spl5_3),
% 3.22/0.81    inference(avatar_contradiction_clause,[],[f529])).
% 3.22/0.81  fof(f529,plain,(
% 3.22/0.81    $false | (~spl5_1 | spl5_3)),
% 3.22/0.81    inference(subsumption_resolution,[],[f528,f498])).
% 3.22/0.81  fof(f498,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl5_1),
% 3.22/0.81    inference(backward_demodulation,[],[f456,f480])).
% 3.22/0.81  fof(f480,plain,(
% 3.22/0.81    sK1 = sK2 | ~spl5_1),
% 3.22/0.81    inference(subsumption_resolution,[],[f479,f44])).
% 3.22/0.81  fof(f479,plain,(
% 3.22/0.81    sK0 = sK2 | sK1 = sK2 | ~spl5_1),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f478])).
% 3.22/0.81  fof(f478,plain,(
% 3.22/0.81    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl5_1),
% 3.22/0.81    inference(resolution,[],[f403,f118])).
% 3.22/0.81  fof(f403,plain,(
% 3.22/0.81    r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_1),
% 3.22/0.81    inference(superposition,[],[f115,f124])).
% 3.22/0.81  fof(f124,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl5_1),
% 3.22/0.81    inference(avatar_component_clause,[],[f122])).
% 3.22/0.81  fof(f115,plain,(
% 3.22/0.81    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 3.22/0.81    inference(equality_resolution,[],[f114])).
% 3.22/0.81  fof(f114,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 3.22/0.81    inference(equality_resolution,[],[f105])).
% 3.22/0.81  fof(f105,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.22/0.81    inference(definition_unfolding,[],[f72,f85])).
% 3.22/0.81  fof(f72,plain,(
% 3.22/0.81    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.22/0.81    inference(cnf_transformation,[],[f42])).
% 3.22/0.81  fof(f456,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1,sK2) | ~spl5_1),
% 3.22/0.81    inference(superposition,[],[f440,f91])).
% 3.22/0.81  fof(f440,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) | ~spl5_1),
% 3.22/0.81    inference(backward_demodulation,[],[f124,f439])).
% 3.22/0.81  fof(f439,plain,(
% 3.22/0.81    sK1 = sK3 | ~spl5_1),
% 3.22/0.81    inference(subsumption_resolution,[],[f438,f45])).
% 3.22/0.81  fof(f438,plain,(
% 3.22/0.81    sK0 = sK3 | sK1 = sK3 | ~spl5_1),
% 3.22/0.81    inference(duplicate_literal_removal,[],[f437])).
% 3.22/0.81  fof(f437,plain,(
% 3.22/0.81    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl5_1),
% 3.22/0.81    inference(resolution,[],[f402,f118])).
% 3.22/0.81  fof(f402,plain,(
% 3.22/0.81    r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_1),
% 3.22/0.81    inference(superposition,[],[f113,f124])).
% 3.22/0.81  fof(f528,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | (~spl5_1 | spl5_3)),
% 3.22/0.81    inference(forward_demodulation,[],[f131,f480])).
% 3.22/0.81  fof(f131,plain,(
% 3.22/0.81    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | spl5_3),
% 3.22/0.81    inference(avatar_component_clause,[],[f130])).
% 3.22/0.81  % SZS output end Proof for theBenchmark
% 3.22/0.81  % (20859)------------------------------
% 3.22/0.81  % (20859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.81  % (20859)Termination reason: Refutation
% 3.22/0.81  
% 3.22/0.81  % (20859)Memory used [KB]: 11385
% 3.22/0.81  % (20859)Time elapsed: 0.391 s
% 3.22/0.81  % (20859)------------------------------
% 3.22/0.81  % (20859)------------------------------
% 3.22/0.82  % (20850)Success in time 0.457 s
%------------------------------------------------------------------------------
