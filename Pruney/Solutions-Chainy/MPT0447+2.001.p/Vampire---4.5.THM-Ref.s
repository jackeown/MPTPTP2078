%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:08 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 195 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  332 ( 718 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2416,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f348,f533,f571,f598,f747,f2408])).

fof(f2408,plain,(
    spl8_17 ),
    inference(avatar_contradiction_clause,[],[f2401])).

fof(f2401,plain,
    ( $false
    | spl8_17 ),
    inference(subsumption_resolution,[],[f328,f2398])).

fof(f2398,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl8_17 ),
    inference(resolution,[],[f770,f750])).

fof(f750,plain,
    ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0))
    | spl8_17 ),
    inference(resolution,[],[f328,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f770,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0,k3_relat_1(sK1)),k1_relat_1(sK0))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f247,f258])).

fof(f258,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f144,f122])).

fof(f122,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f52,f55,f54,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f144,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | r2_hidden(X4,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f128,f121])).

fof(f121,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f67,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f247,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2(X3,k3_relat_1(sK1)),k1_relat_1(sK1))
      | r1_tarski(X3,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f167,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f167,plain,(
    ! [X5] :
      ( r2_hidden(X5,k3_relat_1(sK1))
      | ~ r2_hidden(X5,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f124,f127])).

fof(f127,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f66,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f71,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f66,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f101,f79])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & ~ r2_hidden(sK7(X0,X1,X2),X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & ~ r2_hidden(sK7(X0,X1,X2),X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f328,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl8_17
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f747,plain,
    ( ~ spl8_35
    | ~ spl8_36
    | ~ spl8_37
    | spl8_18 ),
    inference(avatar_split_clause,[],[f744,f330,f460,f457,f454])).

fof(f454,plain,
    ( spl8_35
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f457,plain,
    ( spl8_36
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f460,plain,
    ( spl8_37
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f330,plain,
    ( spl8_18
  <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f744,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl8_18 ),
    inference(resolution,[],[f437,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f437,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl8_18 ),
    inference(resolution,[],[f331,f162])).

fof(f162,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_relat_1(sK1))
      | ~ r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f109,f127])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f95,f79])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f331,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f330])).

fof(f598,plain,(
    spl8_37 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | spl8_37 ),
    inference(subsumption_resolution,[],[f67,f461])).

fof(f461,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl8_37 ),
    inference(avatar_component_clause,[],[f460])).

fof(f571,plain,(
    spl8_36 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | spl8_36 ),
    inference(subsumption_resolution,[],[f66,f458])).

fof(f458,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_36 ),
    inference(avatar_component_clause,[],[f457])).

fof(f533,plain,(
    spl8_35 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | spl8_35 ),
    inference(subsumption_resolution,[],[f65,f455])).

fof(f455,plain,
    ( ~ v1_relat_1(sK0)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f454])).

fof(f65,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f348,plain,
    ( ~ spl8_17
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f347,f330,f327])).

fof(f347,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(global_subsumption,[],[f312])).

fof(f312,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f158,f68])).

fof(f68,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f158,plain,(
    ! [X3] :
      ( r1_tarski(k3_relat_1(sK0),X3)
      | ~ r1_tarski(k2_relat_1(sK0),X3)
      | ~ r1_tarski(k1_relat_1(sK0),X3) ) ),
    inference(superposition,[],[f112,f126])).

fof(f126,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f65,f107])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f99,f79])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n012.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 20:20:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.49  % (10701)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.49  % (10710)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.53  % (10698)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.54  % (10702)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.54  % (10717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.54  % (10709)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.55  % (10699)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.55  % (10723)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.55  % (10694)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (10718)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.55  % (10721)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (10700)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.55  % (10720)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.55  % (10696)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (10697)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.56  % (10695)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.56  % (10724)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.56  % (10712)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.56  % (10715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.56  % (10719)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.56  % (10716)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.56  % (10713)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.56  % (10705)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.57  % (10707)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.57  % (10703)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.57  % (10714)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.57  % (10708)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.57  % (10704)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.57  % (10722)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.58  % (10711)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.73  % (10696)Refutation found. Thanks to Tanya!
% 0.23/0.73  % SZS status Theorem for theBenchmark
% 0.23/0.73  % SZS output start Proof for theBenchmark
% 0.23/0.73  fof(f2416,plain,(
% 0.23/0.73    $false),
% 0.23/0.73    inference(avatar_sat_refutation,[],[f348,f533,f571,f598,f747,f2408])).
% 0.23/0.73  fof(f2408,plain,(
% 0.23/0.73    spl8_17),
% 0.23/0.73    inference(avatar_contradiction_clause,[],[f2401])).
% 0.23/0.73  fof(f2401,plain,(
% 0.23/0.73    $false | spl8_17),
% 0.23/0.73    inference(subsumption_resolution,[],[f328,f2398])).
% 0.23/0.73  fof(f2398,plain,(
% 0.23/0.73    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | spl8_17),
% 0.23/0.73    inference(resolution,[],[f770,f750])).
% 0.23/0.73  fof(f750,plain,(
% 0.23/0.73    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0)) | spl8_17),
% 0.23/0.73    inference(resolution,[],[f328,f85])).
% 0.23/0.73  fof(f85,plain,(
% 0.23/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.23/0.73    inference(cnf_transformation,[],[f50])).
% 0.23/0.73  fof(f50,plain,(
% 0.23/0.73    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 0.23/0.73  fof(f49,plain,(
% 0.23/0.73    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.23/0.73    introduced(choice_axiom,[])).
% 0.23/0.73  fof(f48,plain,(
% 0.23/0.73    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.73    inference(rectify,[],[f47])).
% 0.23/0.73  fof(f47,plain,(
% 0.23/0.73    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.73    inference(nnf_transformation,[],[f33])).
% 0.23/0.73  fof(f33,plain,(
% 0.23/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.73    inference(ennf_transformation,[],[f2])).
% 0.23/0.73  fof(f2,axiom,(
% 0.23/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.73  fof(f770,plain,(
% 0.23/0.73    ( ! [X0] : (~r2_hidden(sK2(X0,k3_relat_1(sK1)),k1_relat_1(sK0)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 0.23/0.73    inference(resolution,[],[f247,f258])).
% 0.23/0.73  fof(f258,plain,(
% 0.23/0.73    ( ! [X1] : (r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK0))) )),
% 0.23/0.73    inference(resolution,[],[f144,f122])).
% 0.23/0.73  fof(f122,plain,(
% 0.23/0.73    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.23/0.73    inference(equality_resolution,[],[f87])).
% 0.23/0.73  fof(f87,plain,(
% 0.23/0.73    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.23/0.73    inference(cnf_transformation,[],[f56])).
% 0.23/0.73  fof(f56,plain,(
% 0.23/0.73    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f52,f55,f54,f53])).
% 0.23/0.73  fof(f53,plain,(
% 0.23/0.73    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.23/0.73    introduced(choice_axiom,[])).
% 0.23/0.73  fof(f54,plain,(
% 0.23/0.73    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.23/0.73    introduced(choice_axiom,[])).
% 0.23/0.73  fof(f55,plain,(
% 0.23/0.73    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.23/0.73    introduced(choice_axiom,[])).
% 0.23/0.73  fof(f52,plain,(
% 0.23/0.73    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.23/0.73    inference(rectify,[],[f51])).
% 0.23/0.73  fof(f51,plain,(
% 0.23/0.73    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.23/0.73    inference(nnf_transformation,[],[f19])).
% 0.23/0.73  fof(f19,axiom,(
% 0.23/0.73    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.23/0.73  fof(f144,plain,(
% 0.23/0.73    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK0) | r2_hidden(X4,k1_relat_1(sK1))) )),
% 0.23/0.73    inference(resolution,[],[f128,f121])).
% 0.23/0.73  fof(f121,plain,(
% 0.23/0.73    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.23/0.73    inference(equality_resolution,[],[f88])).
% 0.23/0.73  fof(f88,plain,(
% 0.23/0.73    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.23/0.73    inference(cnf_transformation,[],[f56])).
% 0.23/0.73  fof(f128,plain,(
% 0.23/0.73    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.23/0.73    inference(resolution,[],[f67,f84])).
% 0.23/0.73  fof(f84,plain,(
% 0.23/0.73    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.23/0.73    inference(cnf_transformation,[],[f50])).
% 0.23/0.73  fof(f67,plain,(
% 0.23/0.73    r1_tarski(sK0,sK1)),
% 0.23/0.73    inference(cnf_transformation,[],[f44])).
% 0.23/0.73  fof(f44,plain,(
% 0.23/0.73    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f43,f42])).
% 0.23/0.73  fof(f42,plain,(
% 0.23/0.73    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.23/0.73    introduced(choice_axiom,[])).
% 0.23/0.73  fof(f43,plain,(
% 0.23/0.73    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 0.23/0.73    introduced(choice_axiom,[])).
% 0.23/0.73  fof(f26,plain,(
% 0.23/0.73    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.23/0.73    inference(flattening,[],[f25])).
% 0.23/0.73  fof(f25,plain,(
% 0.23/0.73    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.23/0.73    inference(ennf_transformation,[],[f24])).
% 0.23/0.73  fof(f24,negated_conjecture,(
% 0.23/0.73    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.73    inference(negated_conjecture,[],[f23])).
% 0.23/0.73  fof(f23,conjecture,(
% 0.23/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.23/0.73  fof(f247,plain,(
% 0.23/0.73    ( ! [X3] : (~r2_hidden(sK2(X3,k3_relat_1(sK1)),k1_relat_1(sK1)) | r1_tarski(X3,k3_relat_1(sK1))) )),
% 0.23/0.73    inference(resolution,[],[f167,f86])).
% 0.23/0.73  fof(f86,plain,(
% 0.23/0.73    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.23/0.73    inference(cnf_transformation,[],[f50])).
% 0.23/0.73  fof(f167,plain,(
% 0.23/0.73    ( ! [X5] : (r2_hidden(X5,k3_relat_1(sK1)) | ~r2_hidden(X5,k1_relat_1(sK1))) )),
% 0.23/0.73    inference(superposition,[],[f124,f127])).
% 0.23/0.73  fof(f127,plain,(
% 0.23/0.73    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.23/0.73    inference(resolution,[],[f66,f107])).
% 0.23/0.73  fof(f107,plain,(
% 0.23/0.73    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.23/0.73    inference(definition_unfolding,[],[f71,f79])).
% 0.23/0.73  fof(f79,plain,(
% 0.23/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.23/0.73    inference(cnf_transformation,[],[f14])).
% 0.23/0.73  fof(f14,axiom,(
% 0.23/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.73  fof(f71,plain,(
% 0.23/0.73    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.73    inference(cnf_transformation,[],[f27])).
% 0.23/0.73  fof(f27,plain,(
% 0.23/0.73    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.73    inference(ennf_transformation,[],[f20])).
% 0.23/0.73  fof(f20,axiom,(
% 0.23/0.73    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.23/0.73  fof(f66,plain,(
% 0.23/0.73    v1_relat_1(sK1)),
% 0.23/0.73    inference(cnf_transformation,[],[f44])).
% 0.23/0.73  fof(f124,plain,(
% 0.23/0.73    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.23/0.73    inference(equality_resolution,[],[f117])).
% 0.23/0.73  fof(f117,plain,(
% 0.23/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 0.23/0.73    inference(definition_unfolding,[],[f101,f79])).
% 0.23/0.73  fof(f101,plain,(
% 0.23/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.23/0.73    inference(cnf_transformation,[],[f64])).
% 0.23/0.73  fof(f64,plain,(
% 0.23/0.73    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f62,f63])).
% 0.23/0.73  fof(f63,plain,(
% 0.23/0.73    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.23/0.73    introduced(choice_axiom,[])).
% 0.23/0.73  fof(f62,plain,(
% 0.23/0.73    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.73    inference(rectify,[],[f61])).
% 0.23/0.73  fof(f61,plain,(
% 0.23/0.73    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.73    inference(flattening,[],[f60])).
% 0.23/0.73  fof(f60,plain,(
% 0.23/0.73    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.73    inference(nnf_transformation,[],[f3])).
% 0.23/0.73  fof(f3,axiom,(
% 0.23/0.73    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.23/0.73  fof(f328,plain,(
% 0.23/0.73    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | spl8_17),
% 0.23/0.73    inference(avatar_component_clause,[],[f327])).
% 0.23/0.73  fof(f327,plain,(
% 0.23/0.73    spl8_17 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.23/0.73    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.23/0.73  fof(f747,plain,(
% 0.23/0.73    ~spl8_35 | ~spl8_36 | ~spl8_37 | spl8_18),
% 0.23/0.73    inference(avatar_split_clause,[],[f744,f330,f460,f457,f454])).
% 0.23/0.73  fof(f454,plain,(
% 0.23/0.73    spl8_35 <=> v1_relat_1(sK0)),
% 0.23/0.73    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.23/0.73  fof(f457,plain,(
% 0.23/0.73    spl8_36 <=> v1_relat_1(sK1)),
% 0.23/0.73    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.23/0.73  fof(f460,plain,(
% 0.23/0.73    spl8_37 <=> r1_tarski(sK0,sK1)),
% 0.23/0.73    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.23/0.73  fof(f330,plain,(
% 0.23/0.73    spl8_18 <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 0.23/0.73    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.23/0.73  fof(f744,plain,(
% 0.23/0.73    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl8_18),
% 0.23/0.73    inference(resolution,[],[f437,f74])).
% 0.23/0.73  fof(f74,plain,(
% 0.23/0.73    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.73    inference(cnf_transformation,[],[f30])).
% 0.23/0.73  fof(f30,plain,(
% 0.23/0.73    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.73    inference(flattening,[],[f29])).
% 0.23/0.73  fof(f29,plain,(
% 0.23/0.73    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.73    inference(ennf_transformation,[],[f22])).
% 0.23/0.73  fof(f22,axiom,(
% 0.23/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.23/0.73  fof(f437,plain,(
% 0.23/0.73    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl8_18),
% 0.23/0.73    inference(resolution,[],[f331,f162])).
% 0.23/0.73  fof(f162,plain,(
% 0.23/0.73    ( ! [X0] : (r1_tarski(X0,k3_relat_1(sK1)) | ~r1_tarski(X0,k2_relat_1(sK1))) )),
% 0.23/0.73    inference(superposition,[],[f109,f127])).
% 0.23/0.73  fof(f109,plain,(
% 0.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.23/0.73    inference(definition_unfolding,[],[f95,f79])).
% 0.23/0.73  fof(f95,plain,(
% 0.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.73    inference(cnf_transformation,[],[f35])).
% 0.23/0.73  fof(f35,plain,(
% 0.23/0.73    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.23/0.73    inference(ennf_transformation,[],[f5])).
% 0.23/0.73  fof(f5,axiom,(
% 0.23/0.73    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.23/0.73  fof(f331,plain,(
% 0.23/0.73    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | spl8_18),
% 0.23/0.73    inference(avatar_component_clause,[],[f330])).
% 0.23/0.73  fof(f598,plain,(
% 0.23/0.73    spl8_37),
% 0.23/0.73    inference(avatar_contradiction_clause,[],[f595])).
% 0.23/0.73  fof(f595,plain,(
% 0.23/0.73    $false | spl8_37),
% 0.23/0.73    inference(subsumption_resolution,[],[f67,f461])).
% 0.23/0.73  fof(f461,plain,(
% 0.23/0.73    ~r1_tarski(sK0,sK1) | spl8_37),
% 0.23/0.73    inference(avatar_component_clause,[],[f460])).
% 0.23/0.73  fof(f571,plain,(
% 0.23/0.73    spl8_36),
% 0.23/0.73    inference(avatar_contradiction_clause,[],[f570])).
% 0.23/0.73  fof(f570,plain,(
% 0.23/0.73    $false | spl8_36),
% 0.23/0.73    inference(subsumption_resolution,[],[f66,f458])).
% 0.23/0.73  fof(f458,plain,(
% 0.23/0.73    ~v1_relat_1(sK1) | spl8_36),
% 0.23/0.73    inference(avatar_component_clause,[],[f457])).
% 0.23/0.73  fof(f533,plain,(
% 0.23/0.73    spl8_35),
% 0.23/0.73    inference(avatar_contradiction_clause,[],[f532])).
% 0.23/0.73  fof(f532,plain,(
% 0.23/0.73    $false | spl8_35),
% 0.23/0.73    inference(subsumption_resolution,[],[f65,f455])).
% 0.23/0.73  fof(f455,plain,(
% 0.23/0.73    ~v1_relat_1(sK0) | spl8_35),
% 0.23/0.73    inference(avatar_component_clause,[],[f454])).
% 0.23/0.73  fof(f65,plain,(
% 0.23/0.73    v1_relat_1(sK0)),
% 0.23/0.73    inference(cnf_transformation,[],[f44])).
% 0.23/0.73  fof(f348,plain,(
% 0.23/0.73    ~spl8_17 | ~spl8_18),
% 0.23/0.73    inference(avatar_split_clause,[],[f347,f330,f327])).
% 0.23/0.73  fof(f347,plain,(
% 0.23/0.73    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.23/0.73    inference(global_subsumption,[],[f312])).
% 0.23/0.73  fof(f312,plain,(
% 0.23/0.73    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.23/0.73    inference(resolution,[],[f158,f68])).
% 0.23/0.73  fof(f68,plain,(
% 0.23/0.73    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.23/0.73    inference(cnf_transformation,[],[f44])).
% 0.23/0.73  fof(f158,plain,(
% 0.23/0.73    ( ! [X3] : (r1_tarski(k3_relat_1(sK0),X3) | ~r1_tarski(k2_relat_1(sK0),X3) | ~r1_tarski(k1_relat_1(sK0),X3)) )),
% 0.23/0.73    inference(superposition,[],[f112,f126])).
% 0.23/0.73  fof(f126,plain,(
% 0.23/0.73    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.23/0.73    inference(resolution,[],[f65,f107])).
% 0.23/0.73  fof(f112,plain,(
% 0.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.73    inference(definition_unfolding,[],[f99,f79])).
% 0.23/0.73  fof(f99,plain,(
% 0.23/0.73    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.73    inference(cnf_transformation,[],[f41])).
% 0.23/0.73  fof(f41,plain,(
% 0.23/0.73    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.23/0.73    inference(flattening,[],[f40])).
% 0.23/0.73  fof(f40,plain,(
% 0.23/0.73    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.23/0.73    inference(ennf_transformation,[],[f12])).
% 0.23/0.73  fof(f12,axiom,(
% 0.23/0.73    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.23/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.23/0.73  % SZS output end Proof for theBenchmark
% 0.23/0.73  % (10696)------------------------------
% 0.23/0.73  % (10696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.73  % (10696)Termination reason: Refutation
% 0.23/0.73  
% 0.23/0.73  % (10696)Memory used [KB]: 12665
% 0.23/0.73  % (10696)Time elapsed: 0.306 s
% 0.23/0.73  % (10696)------------------------------
% 0.23/0.73  % (10696)------------------------------
% 0.23/0.73  % (10693)Success in time 0.362 s
%------------------------------------------------------------------------------
