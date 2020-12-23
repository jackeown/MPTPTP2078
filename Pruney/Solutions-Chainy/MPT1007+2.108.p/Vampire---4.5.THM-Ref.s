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
% DateTime   : Thu Dec  3 13:04:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 127 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  263 ( 443 expanded)
%              Number of equality atoms :  108 ( 166 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f93,f110,f116])).

fof(f116,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_2 ),
    inference(superposition,[],[f33,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f33,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f110,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl6_3 ),
    inference(resolution,[],[f95,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f95,plain,
    ( ~ sP0(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f94,f34])).

fof(f34,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK4,X0),sK3)
        | ~ sP0(X0,sK2,sK2,sK2,sK2,sK2,sK2,sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f90,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X7,X7,X6,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(resolution,[],[f44,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f55,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(definition_folding,[],[f16,f18,f17])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X9,X7) ) ),
    inference(cnf_transformation,[],[f25])).

% (30931)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X8,X7) )
          & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X8,X7) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
        | r2_hidden(k1_funct_1(sK4,X0),sK3) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_3
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
        | r2_hidden(k1_funct_1(sK4,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f93,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,(
    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f31,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,
    ( ~ v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_1
  <=> v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f91,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f79,f89,f85,f81])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
      | k1_xboole_0 = sK3
      | ~ v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
      | r2_hidden(k1_funct_1(sK4,X0),sK3) ) ),
    inference(resolution,[],[f78,f63])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f32,f62])).

fof(f32,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK4,X2,X0)
      | r2_hidden(k1_funct_1(sK4,X1),X0) ) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:31:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (30933)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (30933)Refutation not found, incomplete strategy% (30933)------------------------------
% 0.20/0.51  % (30933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30951)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (30941)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (30933)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30933)Memory used [KB]: 6268
% 0.20/0.51  % (30933)Time elapsed: 0.089 s
% 0.20/0.51  % (30933)------------------------------
% 0.20/0.51  % (30933)------------------------------
% 0.20/0.51  % (30934)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (30932)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (30935)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (30929)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (30941)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f91,f93,f110,f116])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ~spl6_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    $false | ~spl6_2),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | ~spl6_2),
% 0.20/0.52    inference(superposition,[],[f33,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    k1_xboole_0 = sK3 | ~spl6_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    spl6_2 <=> k1_xboole_0 = sK3),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k1_xboole_0 != sK3),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ~spl6_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    $false | ~spl6_3),
% 0.20/0.52    inference(resolution,[],[f95,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.20/0.52    inference(equality_resolution,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.52    inference(rectify,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X8,X6,X5,X4,X3,X2,X1,X0] : (sP0(X8,X6,X5,X4,X3,X2,X1,X0) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ~sP0(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl6_3),
% 0.20/0.52    inference(resolution,[],[f94,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),sK3) | ~sP0(X0,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ) | ~spl6_3),
% 0.20/0.52    inference(resolution,[],[f90,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X0,k6_enumset1(X7,X7,X6,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.20/0.52    inference(resolution,[],[f44,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.52    inference(equality_resolution,[],[f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 0.20/0.52    inference(definition_unfolding,[],[f55,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 0.20/0.52    inference(nnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.20/0.52    inference(definition_folding,[],[f16,f18,f17])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X7)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  % (30931)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7))) => ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.52    inference(rectify,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.52    inference(nnf_transformation,[],[f18])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(k1_funct_1(sK4,X0),sK3)) ) | ~spl6_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    spl6_3 <=> ! [X0] : (~r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(k1_funct_1(sK4,X0),sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl6_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    $false | spl6_1),
% 0.20/0.52    inference(resolution,[],[f83,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f35,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f36,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f37,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f38,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f40,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f41,f42])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ~v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) | spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl6_1 <=> v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~spl6_1 | spl6_2 | spl6_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f79,f89,f85,f81])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | k1_xboole_0 = sK3 | ~v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) | r2_hidden(k1_funct_1(sK4,X0),sK3)) )),
% 0.20/0.52    inference(resolution,[],[f78,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f62])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK4,X2,X0) | r2_hidden(k1_funct_1(sK4,X1),X0)) )),
% 0.20/0.52    inference(resolution,[],[f39,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (30941)------------------------------
% 0.20/0.52  % (30941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30941)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (30941)Memory used [KB]: 6268
% 0.20/0.52  % (30941)Time elapsed: 0.102 s
% 0.20/0.52  % (30941)------------------------------
% 0.20/0.52  % (30941)------------------------------
% 0.20/0.52  % (30928)Success in time 0.157 s
%------------------------------------------------------------------------------
