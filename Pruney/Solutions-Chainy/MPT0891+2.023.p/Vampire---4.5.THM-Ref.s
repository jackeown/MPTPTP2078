%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:09 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 709 expanded)
%              Number of leaves         :   24 ( 207 expanded)
%              Depth                    :   20
%              Number of atoms          :  549 (4381 expanded)
%              Number of equality atoms :  263 (1939 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1087,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f479,f543,f571,f652,f735,f997,f1012,f1077])).

fof(f1077,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f1064])).

fof(f1064,plain,
    ( $false
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f123,f59,f478,f55])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK6(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f478,plain,
    ( k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)) = sK6(k2_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl7_13
  <=> k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)) = sK6(k2_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f59,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f123,plain,(
    ! [X8,X9] : k1_xboole_0 != k2_tarski(X8,X9) ),
    inference(subsumption_resolution,[],[f121,f59])).

fof(f121,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 != k2_tarski(X8,X9)
      | ~ r2_hidden(X9,k2_tarski(X8,X9)) ) ),
    inference(superposition,[],[f39,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f100,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f1012,plain,
    ( spl7_10
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f1011,f95,f90,f85,f80,f67,f272])).

fof(f272,plain,
    ( spl7_10
  <=> sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f67,plain,
    ( spl7_1
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f80,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f85,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f90,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f95,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1011,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f1010,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK0
    | spl7_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1010,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f1009,f92])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl7_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1009,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f1008,f87])).

fof(f87,plain,
    ( k1_xboole_0 != sK2
    | spl7_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1008,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1007,f82])).

fof(f82,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1007,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(superposition,[],[f36,f69])).

fof(f69,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f997,plain,(
    ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f985])).

fof(f985,plain,
    ( $false
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f123,f59,f542,f56])).

fof(f56,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK6(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f542,plain,
    ( k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = sK6(k2_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl7_14
  <=> k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = sK6(k2_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f735,plain,
    ( spl7_8
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f734,f95,f90,f85,f80,f71,f164])).

fof(f164,plain,
    ( spl7_8
  <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f71,plain,
    ( spl7_2
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f734,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f733,f97])).

fof(f733,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f732,f92])).

fof(f732,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f731,f87])).

fof(f731,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f730,f82])).

fof(f730,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(superposition,[],[f36,f73])).

fof(f73,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f652,plain,(
    ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f123,f59,f631,f599])).

fof(f599,plain,
    ( ! [X5] :
        ( sK3 != sK6(X5)
        | ~ r2_hidden(sK3,X5)
        | k1_xboole_0 = X5 )
    | ~ spl7_17 ),
    inference(superposition,[],[f115,f570])).

fof(f570,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl7_17
  <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != sK6(X3)
      | ~ r2_hidden(X2,X3)
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f56,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f631,plain,
    ( ! [X0] : sK6(k2_tarski(X0,sK3)) = X0
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f630,f59])).

fof(f630,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k2_tarski(X0,sK3))
        | sK6(k2_tarski(X0,sK3)) = X0 )
    | ~ spl7_17 ),
    inference(equality_resolution,[],[f597])).

fof(f597,plain,
    ( ! [X2,X3] :
        ( sK3 != X2
        | ~ r2_hidden(sK3,k2_tarski(X3,X2))
        | sK6(k2_tarski(X3,X2)) = X3 )
    | ~ spl7_17 ),
    inference(superposition,[],[f231,f570])).

fof(f231,plain,(
    ! [X19,X17,X15,X18,X16] :
      ( k3_mcart_1(X17,X18,X19) != X16
      | ~ r2_hidden(X19,k2_tarski(X15,X16))
      | sK6(k2_tarski(X15,X16)) = X15 ) ),
    inference(subsumption_resolution,[],[f224,f123])).

fof(f224,plain,(
    ! [X19,X17,X15,X18,X16] :
      ( k3_mcart_1(X17,X18,X19) != X16
      | ~ r2_hidden(X19,k2_tarski(X15,X16))
      | k1_xboole_0 = k2_tarski(X15,X16)
      | sK6(k2_tarski(X15,X16)) = X15 ) ),
    inference(superposition,[],[f115,f219])).

fof(f219,plain,(
    ! [X4,X5] :
      ( sK6(k2_tarski(X4,X5)) = X5
      | sK6(k2_tarski(X4,X5)) = X4 ) ),
    inference(subsumption_resolution,[],[f105,f123])).

fof(f105,plain,(
    ! [X4,X5] :
      ( sK6(k2_tarski(X4,X5)) = X4
      | sK6(k2_tarski(X4,X5)) = X5
      | k1_xboole_0 = k2_tarski(X4,X5) ) ),
    inference(resolution,[],[f62,f54])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f571,plain,
    ( spl7_17
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f566,f95,f90,f85,f80,f75,f568])).

fof(f75,plain,
    ( spl7_3
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f566,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f565,f97])).

fof(f565,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f564,f92])).

fof(f564,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f563,f87])).

fof(f563,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f549,f82])).

fof(f549,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_3 ),
    inference(superposition,[],[f36,f77])).

fof(f77,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f543,plain,
    ( spl7_14
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f538,f164,f540])).

fof(f538,plain,
    ( k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = sK6(k2_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3))
    | ~ spl7_8 ),
    inference(resolution,[],[f520,f61])).

fof(f61,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f520,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_tarski(X0,sK3))
        | sK6(k2_tarski(X0,sK3)) = X0 )
    | ~ spl7_8 ),
    inference(equality_resolution,[],[f495])).

fof(f495,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_tarski(X0,X1))
        | sK6(k2_tarski(X0,X1)) = X0 )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f493,f123])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK6(k2_tarski(X0,X1)) = X0 )
    | ~ spl7_8 ),
    inference(superposition,[],[f487,f219])).

fof(f487,plain,
    ( ! [X0] :
        ( sK3 != sK6(X0)
        | ~ r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(superposition,[],[f114,f166])).

fof(f166,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != sK6(X3)
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f55,f53])).

fof(f479,plain,
    ( spl7_13
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f474,f272,f476])).

fof(f474,plain,
    ( k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)) = sK6(k2_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3))
    | ~ spl7_10 ),
    inference(resolution,[],[f463,f61])).

fof(f463,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_tarski(X0,sK3))
        | sK6(k2_tarski(X0,sK3)) = X0 )
    | ~ spl7_10 ),
    inference(equality_resolution,[],[f329])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_tarski(X0,X1))
        | sK6(k2_tarski(X0,X1)) = X0 )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f328,f123])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( sK3 != X1
        | ~ r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK6(k2_tarski(X0,X1)) = X0 )
    | ~ spl7_10 ),
    inference(superposition,[],[f282,f219])).

fof(f282,plain,
    ( ! [X0] :
        ( sK3 != sK6(X0)
        | ~ r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_10 ),
    inference(superposition,[],[f114,f274])).

fof(f274,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f272])).

fof(f98,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15,f14])).

fof(f14,plain,
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
          ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
            | k6_mcart_1(sK0,sK1,sK2,X3) = X3
            | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
          | k6_mcart_1(sK0,sK1,sK2,X3) = X3
          | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f93,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,
    ( spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f35,f75,f71,f67])).

fof(f35,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:18:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (32640)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (32643)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (32657)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (32648)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (32632)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (32646)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (32648)Refutation not found, incomplete strategy% (32648)------------------------------
% 0.22/0.54  % (32648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32634)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32642)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (32648)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32648)Memory used [KB]: 1791
% 0.22/0.54  % (32648)Time elapsed: 0.126 s
% 0.22/0.54  % (32648)------------------------------
% 0.22/0.54  % (32648)------------------------------
% 0.22/0.54  % (32636)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (32654)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (32657)Refutation not found, incomplete strategy% (32657)------------------------------
% 0.22/0.54  % (32657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32657)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32657)Memory used [KB]: 6268
% 0.22/0.54  % (32657)Time elapsed: 0.124 s
% 0.22/0.54  % (32657)------------------------------
% 0.22/0.54  % (32657)------------------------------
% 0.22/0.54  % (32635)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (32632)Refutation not found, incomplete strategy% (32632)------------------------------
% 0.22/0.54  % (32632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32632)Memory used [KB]: 1663
% 0.22/0.54  % (32632)Time elapsed: 0.098 s
% 0.22/0.54  % (32632)------------------------------
% 0.22/0.54  % (32632)------------------------------
% 0.22/0.55  % (32655)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (32631)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (32633)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (32652)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (32660)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (32639)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (32660)Refutation not found, incomplete strategy% (32660)------------------------------
% 0.22/0.55  % (32660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32660)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32660)Memory used [KB]: 1663
% 0.22/0.55  % (32660)Time elapsed: 0.137 s
% 0.22/0.55  % (32660)------------------------------
% 0.22/0.55  % (32660)------------------------------
% 0.22/0.55  % (32659)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (32643)Refutation not found, incomplete strategy% (32643)------------------------------
% 0.22/0.55  % (32643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32643)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32643)Memory used [KB]: 10618
% 0.22/0.55  % (32643)Time elapsed: 0.133 s
% 0.22/0.55  % (32643)------------------------------
% 0.22/0.55  % (32643)------------------------------
% 0.22/0.55  % (32650)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (32647)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (32638)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (32658)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (32647)Refutation not found, incomplete strategy% (32647)------------------------------
% 0.22/0.56  % (32647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32647)Memory used [KB]: 10618
% 0.22/0.56  % (32647)Time elapsed: 0.144 s
% 0.22/0.56  % (32647)------------------------------
% 0.22/0.56  % (32647)------------------------------
% 0.22/0.56  % (32637)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (32651)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (32658)Refutation not found, incomplete strategy% (32658)------------------------------
% 0.22/0.56  % (32658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32658)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32658)Memory used [KB]: 6268
% 0.22/0.56  % (32658)Time elapsed: 0.147 s
% 0.22/0.56  % (32658)------------------------------
% 0.22/0.56  % (32658)------------------------------
% 0.22/0.56  % (32644)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (32649)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (32649)Refutation not found, incomplete strategy% (32649)------------------------------
% 0.22/0.56  % (32649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32649)Memory used [KB]: 1663
% 0.22/0.56  % (32649)Time elapsed: 0.145 s
% 0.22/0.56  % (32649)------------------------------
% 0.22/0.56  % (32649)------------------------------
% 0.22/0.56  % (32656)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (32641)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (32655)Refutation not found, incomplete strategy% (32655)------------------------------
% 0.22/0.57  % (32655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (32655)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (32655)Memory used [KB]: 10746
% 0.22/0.57  % (32655)Time elapsed: 0.157 s
% 0.22/0.57  % (32655)------------------------------
% 0.22/0.57  % (32655)------------------------------
% 1.71/0.58  % (32653)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.71/0.59  % (32645)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.71/0.59  % (32645)Refutation not found, incomplete strategy% (32645)------------------------------
% 1.71/0.59  % (32645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (32645)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.61  
% 1.85/0.61  % (32645)Memory used [KB]: 1663
% 1.85/0.61  % (32645)Time elapsed: 0.157 s
% 1.85/0.61  % (32645)------------------------------
% 1.85/0.61  % (32645)------------------------------
% 2.09/0.66  % (32664)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.09/0.68  % (32652)Refutation found. Thanks to Tanya!
% 2.09/0.68  % SZS status Theorem for theBenchmark
% 2.09/0.68  % SZS output start Proof for theBenchmark
% 2.09/0.68  fof(f1087,plain,(
% 2.09/0.68    $false),
% 2.09/0.68    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f479,f543,f571,f652,f735,f997,f1012,f1077])).
% 2.09/0.68  fof(f1077,plain,(
% 2.09/0.68    ~spl7_13),
% 2.09/0.68    inference(avatar_contradiction_clause,[],[f1064])).
% 2.09/0.68  fof(f1064,plain,(
% 2.09/0.68    $false | ~spl7_13),
% 2.09/0.68    inference(unit_resulting_resolution,[],[f123,f59,f478,f55])).
% 2.09/0.68  fof(f55,plain,(
% 2.09/0.68    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK6(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.09/0.68    inference(cnf_transformation,[],[f30])).
% 2.09/0.68  fof(f30,plain,(
% 2.09/0.68    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 2.09/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f29])).
% 2.09/0.68  fof(f29,plain,(
% 2.09/0.68    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 2.09/0.68    introduced(choice_axiom,[])).
% 2.09/0.68  fof(f13,plain,(
% 2.09/0.68    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.09/0.68    inference(ennf_transformation,[],[f8])).
% 2.09/0.68  fof(f8,axiom,(
% 2.09/0.68    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.09/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 2.09/0.68  fof(f478,plain,(
% 2.09/0.68    k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)) = sK6(k2_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)) | ~spl7_13),
% 2.09/0.68    inference(avatar_component_clause,[],[f476])).
% 2.09/0.68  fof(f476,plain,(
% 2.09/0.68    spl7_13 <=> k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)) = sK6(k2_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3))),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.09/0.68  fof(f59,plain,(
% 2.09/0.68    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.09/0.68    inference(equality_resolution,[],[f58])).
% 2.09/0.68  fof(f58,plain,(
% 2.09/0.68    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.09/0.68    inference(equality_resolution,[],[f43])).
% 2.09/0.68  fof(f43,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.09/0.68    inference(cnf_transformation,[],[f23])).
% 2.09/0.68  fof(f23,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.09/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 2.09/0.68  fof(f22,plain,(
% 2.09/0.68    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.09/0.68    introduced(choice_axiom,[])).
% 2.09/0.68  fof(f21,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.09/0.68    inference(rectify,[],[f20])).
% 2.09/0.68  fof(f20,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.09/0.68    inference(flattening,[],[f19])).
% 2.09/0.68  fof(f19,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.09/0.68    inference(nnf_transformation,[],[f2])).
% 2.09/0.68  fof(f2,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.09/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.09/0.68  fof(f123,plain,(
% 2.09/0.68    ( ! [X8,X9] : (k1_xboole_0 != k2_tarski(X8,X9)) )),
% 2.09/0.68    inference(subsumption_resolution,[],[f121,f59])).
% 2.09/0.68  fof(f121,plain,(
% 2.09/0.68    ( ! [X8,X9] : (k1_xboole_0 != k2_tarski(X8,X9) | ~r2_hidden(X9,k2_tarski(X8,X9))) )),
% 2.09/0.68    inference(superposition,[],[f39,f113])).
% 2.09/0.68  fof(f113,plain,(
% 2.09/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.09/0.68    inference(duplicate_literal_removal,[],[f109])).
% 2.09/0.68  fof(f109,plain,(
% 2.09/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.09/0.68    inference(resolution,[],[f100,f99])).
% 2.09/0.68  fof(f99,plain,(
% 2.09/0.68    ( ! [X0,X1] : (~r2_hidden(sK6(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.09/0.68    inference(resolution,[],[f64,f54])).
% 2.09/0.68  fof(f54,plain,(
% 2.09/0.68    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.09/0.68    inference(cnf_transformation,[],[f30])).
% 2.09/0.68  fof(f64,plain,(
% 2.09/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.09/0.68    inference(equality_resolution,[],[f48])).
% 2.09/0.68  fof(f48,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.09/0.68    inference(cnf_transformation,[],[f28])).
% 2.09/0.68  fof(f28,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 2.09/0.68  fof(f27,plain,(
% 2.09/0.68    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.09/0.68    introduced(choice_axiom,[])).
% 2.09/0.68  fof(f26,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.68    inference(rectify,[],[f25])).
% 2.09/0.68  fof(f25,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.68    inference(flattening,[],[f24])).
% 2.09/0.68  fof(f24,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.09/0.68    inference(nnf_transformation,[],[f1])).
% 2.09/0.68  fof(f1,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.09/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.09/0.68  fof(f100,plain,(
% 2.09/0.68    ( ! [X0,X1] : (r2_hidden(sK6(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.09/0.68    inference(resolution,[],[f65,f54])).
% 2.09/0.68  fof(f65,plain,(
% 2.09/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.09/0.68    inference(equality_resolution,[],[f47])).
% 2.09/0.68  fof(f47,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.09/0.68    inference(cnf_transformation,[],[f28])).
% 2.09/0.68  fof(f39,plain,(
% 2.09/0.68    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f18])).
% 2.09/0.68  fof(f18,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.09/0.68    inference(flattening,[],[f17])).
% 2.09/0.68  fof(f17,plain,(
% 2.09/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.09/0.68    inference(nnf_transformation,[],[f4])).
% 2.09/0.68  fof(f4,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.09/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.09/0.68  fof(f1012,plain,(
% 2.09/0.68    spl7_10 | ~spl7_1 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 2.09/0.68    inference(avatar_split_clause,[],[f1011,f95,f90,f85,f80,f67,f272])).
% 2.09/0.68  fof(f272,plain,(
% 2.09/0.68    spl7_10 <=> sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.09/0.68  fof(f67,plain,(
% 2.09/0.68    spl7_1 <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.09/0.68  fof(f80,plain,(
% 2.09/0.68    spl7_4 <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.09/0.68  fof(f85,plain,(
% 2.09/0.68    spl7_5 <=> k1_xboole_0 = sK2),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.09/0.68  fof(f90,plain,(
% 2.09/0.68    spl7_6 <=> k1_xboole_0 = sK1),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.09/0.68  fof(f95,plain,(
% 2.09/0.68    spl7_7 <=> k1_xboole_0 = sK0),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.09/0.68  fof(f1011,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | (~spl7_1 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1010,f97])).
% 2.09/0.68  fof(f97,plain,(
% 2.09/0.68    k1_xboole_0 != sK0 | spl7_7),
% 2.09/0.68    inference(avatar_component_clause,[],[f95])).
% 2.09/0.68  fof(f1010,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (~spl7_1 | ~spl7_4 | spl7_5 | spl7_6)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1009,f92])).
% 2.09/0.68  fof(f92,plain,(
% 2.09/0.68    k1_xboole_0 != sK1 | spl7_6),
% 2.09/0.68    inference(avatar_component_clause,[],[f90])).
% 2.09/0.68  fof(f1009,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_1 | ~spl7_4 | spl7_5)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1008,f87])).
% 2.09/0.68  fof(f87,plain,(
% 2.09/0.68    k1_xboole_0 != sK2 | spl7_5),
% 2.09/0.68    inference(avatar_component_clause,[],[f85])).
% 2.09/0.68  fof(f1008,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_1 | ~spl7_4)),
% 2.09/0.68    inference(subsumption_resolution,[],[f1007,f82])).
% 2.09/0.68  fof(f82,plain,(
% 2.09/0.68    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | ~spl7_4),
% 2.09/0.68    inference(avatar_component_clause,[],[f80])).
% 2.09/0.68  fof(f1007,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_1),
% 2.09/0.68    inference(superposition,[],[f36,f69])).
% 2.09/0.68  fof(f69,plain,(
% 2.09/0.68    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_1),
% 2.09/0.68    inference(avatar_component_clause,[],[f67])).
% 2.09/0.68  fof(f36,plain,(
% 2.09/0.68    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.09/0.68    inference(cnf_transformation,[],[f12])).
% 2.09/0.68  fof(f12,plain,(
% 2.09/0.68    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.09/0.68    inference(ennf_transformation,[],[f7])).
% 2.09/0.68  fof(f7,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.09/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 2.09/0.68  fof(f997,plain,(
% 2.09/0.68    ~spl7_14),
% 2.09/0.68    inference(avatar_contradiction_clause,[],[f985])).
% 2.09/0.68  fof(f985,plain,(
% 2.09/0.68    $false | ~spl7_14),
% 2.09/0.68    inference(unit_resulting_resolution,[],[f123,f59,f542,f56])).
% 2.09/0.68  fof(f56,plain,(
% 2.09/0.68    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK6(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.09/0.68    inference(cnf_transformation,[],[f30])).
% 2.09/0.68  fof(f542,plain,(
% 2.09/0.68    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = sK6(k2_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3)) | ~spl7_14),
% 2.09/0.68    inference(avatar_component_clause,[],[f540])).
% 2.09/0.68  fof(f540,plain,(
% 2.09/0.68    spl7_14 <=> k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = sK6(k2_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3))),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.09/0.68  fof(f735,plain,(
% 2.09/0.68    spl7_8 | ~spl7_2 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 2.09/0.68    inference(avatar_split_clause,[],[f734,f95,f90,f85,f80,f71,f164])).
% 2.09/0.68  fof(f164,plain,(
% 2.09/0.68    spl7_8 <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.09/0.68  fof(f71,plain,(
% 2.09/0.68    spl7_2 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.09/0.68  fof(f734,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | (~spl7_2 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7)),
% 2.09/0.68    inference(subsumption_resolution,[],[f733,f97])).
% 2.09/0.68  fof(f733,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_4 | spl7_5 | spl7_6)),
% 2.09/0.68    inference(subsumption_resolution,[],[f732,f92])).
% 2.09/0.68  fof(f732,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_4 | spl7_5)),
% 2.09/0.68    inference(subsumption_resolution,[],[f731,f87])).
% 2.09/0.68  fof(f731,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_4)),
% 2.09/0.68    inference(subsumption_resolution,[],[f730,f82])).
% 2.09/0.68  fof(f730,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_2),
% 2.09/0.68    inference(superposition,[],[f36,f73])).
% 2.09/0.68  fof(f73,plain,(
% 2.09/0.68    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_2),
% 2.09/0.68    inference(avatar_component_clause,[],[f71])).
% 2.09/0.68  fof(f652,plain,(
% 2.09/0.68    ~spl7_17),
% 2.09/0.68    inference(avatar_contradiction_clause,[],[f637])).
% 2.09/0.68  fof(f637,plain,(
% 2.09/0.68    $false | ~spl7_17),
% 2.09/0.68    inference(unit_resulting_resolution,[],[f123,f59,f631,f599])).
% 2.09/0.68  fof(f599,plain,(
% 2.09/0.68    ( ! [X5] : (sK3 != sK6(X5) | ~r2_hidden(sK3,X5) | k1_xboole_0 = X5) ) | ~spl7_17),
% 2.09/0.68    inference(superposition,[],[f115,f570])).
% 2.09/0.68  fof(f570,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | ~spl7_17),
% 2.09/0.68    inference(avatar_component_clause,[],[f568])).
% 2.09/0.68  fof(f568,plain,(
% 2.09/0.68    spl7_17 <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.09/0.68  fof(f115,plain,(
% 2.09/0.68    ( ! [X2,X0,X3,X1] : (k3_mcart_1(X0,X1,X2) != sK6(X3) | ~r2_hidden(X2,X3) | k1_xboole_0 = X3) )),
% 2.09/0.68    inference(superposition,[],[f56,f53])).
% 2.09/0.68  fof(f53,plain,(
% 2.09/0.68    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.09/0.68    inference(cnf_transformation,[],[f5])).
% 2.09/0.68  fof(f5,axiom,(
% 2.09/0.68    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.09/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.09/0.68  fof(f631,plain,(
% 2.09/0.68    ( ! [X0] : (sK6(k2_tarski(X0,sK3)) = X0) ) | ~spl7_17),
% 2.09/0.68    inference(subsumption_resolution,[],[f630,f59])).
% 2.09/0.68  fof(f630,plain,(
% 2.09/0.68    ( ! [X0] : (~r2_hidden(sK3,k2_tarski(X0,sK3)) | sK6(k2_tarski(X0,sK3)) = X0) ) | ~spl7_17),
% 2.09/0.68    inference(equality_resolution,[],[f597])).
% 2.09/0.68  fof(f597,plain,(
% 2.09/0.68    ( ! [X2,X3] : (sK3 != X2 | ~r2_hidden(sK3,k2_tarski(X3,X2)) | sK6(k2_tarski(X3,X2)) = X3) ) | ~spl7_17),
% 2.09/0.68    inference(superposition,[],[f231,f570])).
% 2.09/0.68  fof(f231,plain,(
% 2.09/0.68    ( ! [X19,X17,X15,X18,X16] : (k3_mcart_1(X17,X18,X19) != X16 | ~r2_hidden(X19,k2_tarski(X15,X16)) | sK6(k2_tarski(X15,X16)) = X15) )),
% 2.09/0.68    inference(subsumption_resolution,[],[f224,f123])).
% 2.09/0.68  fof(f224,plain,(
% 2.09/0.68    ( ! [X19,X17,X15,X18,X16] : (k3_mcart_1(X17,X18,X19) != X16 | ~r2_hidden(X19,k2_tarski(X15,X16)) | k1_xboole_0 = k2_tarski(X15,X16) | sK6(k2_tarski(X15,X16)) = X15) )),
% 2.09/0.68    inference(superposition,[],[f115,f219])).
% 2.09/0.68  fof(f219,plain,(
% 2.09/0.68    ( ! [X4,X5] : (sK6(k2_tarski(X4,X5)) = X5 | sK6(k2_tarski(X4,X5)) = X4) )),
% 2.09/0.68    inference(subsumption_resolution,[],[f105,f123])).
% 2.09/0.68  fof(f105,plain,(
% 2.09/0.68    ( ! [X4,X5] : (sK6(k2_tarski(X4,X5)) = X4 | sK6(k2_tarski(X4,X5)) = X5 | k1_xboole_0 = k2_tarski(X4,X5)) )),
% 2.09/0.68    inference(resolution,[],[f62,f54])).
% 2.09/0.68  fof(f62,plain,(
% 2.09/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.09/0.68    inference(equality_resolution,[],[f41])).
% 2.09/0.68  fof(f41,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.09/0.68    inference(cnf_transformation,[],[f23])).
% 2.09/0.68  fof(f571,plain,(
% 2.09/0.68    spl7_17 | ~spl7_3 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 2.09/0.68    inference(avatar_split_clause,[],[f566,f95,f90,f85,f80,f75,f568])).
% 2.09/0.68  fof(f75,plain,(
% 2.09/0.68    spl7_3 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 2.09/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.09/0.68  fof(f566,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | (~spl7_3 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7)),
% 2.09/0.68    inference(subsumption_resolution,[],[f565,f97])).
% 2.09/0.68  fof(f565,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | k1_xboole_0 = sK0 | (~spl7_3 | ~spl7_4 | spl7_5 | spl7_6)),
% 2.09/0.68    inference(subsumption_resolution,[],[f564,f92])).
% 2.09/0.68  fof(f564,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_3 | ~spl7_4 | spl7_5)),
% 2.09/0.68    inference(subsumption_resolution,[],[f563,f87])).
% 2.09/0.68  fof(f563,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_3 | ~spl7_4)),
% 2.09/0.68    inference(subsumption_resolution,[],[f549,f82])).
% 2.09/0.68  fof(f549,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_3),
% 2.09/0.68    inference(superposition,[],[f36,f77])).
% 2.09/0.68  fof(f77,plain,(
% 2.09/0.68    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_3),
% 2.09/0.68    inference(avatar_component_clause,[],[f75])).
% 2.09/0.68  fof(f543,plain,(
% 2.09/0.68    spl7_14 | ~spl7_8),
% 2.09/0.68    inference(avatar_split_clause,[],[f538,f164,f540])).
% 2.09/0.68  fof(f538,plain,(
% 2.09/0.68    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3) = sK6(k2_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),sK3)) | ~spl7_8),
% 2.09/0.68    inference(resolution,[],[f520,f61])).
% 2.09/0.68  fof(f61,plain,(
% 2.09/0.68    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.09/0.68    inference(equality_resolution,[],[f60])).
% 2.09/0.68  fof(f60,plain,(
% 2.09/0.68    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.09/0.68    inference(equality_resolution,[],[f42])).
% 2.09/0.68  fof(f42,plain,(
% 2.09/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.09/0.68    inference(cnf_transformation,[],[f23])).
% 2.09/0.68  fof(f520,plain,(
% 2.09/0.68    ( ! [X0] : (~r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_tarski(X0,sK3)) | sK6(k2_tarski(X0,sK3)) = X0) ) | ~spl7_8),
% 2.09/0.68    inference(equality_resolution,[],[f495])).
% 2.09/0.68  fof(f495,plain,(
% 2.09/0.68    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_tarski(X0,X1)) | sK6(k2_tarski(X0,X1)) = X0) ) | ~spl7_8),
% 2.09/0.68    inference(subsumption_resolution,[],[f493,f123])).
% 2.09/0.68  fof(f493,plain,(
% 2.09/0.68    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK6(k2_tarski(X0,X1)) = X0) ) | ~spl7_8),
% 2.09/0.68    inference(superposition,[],[f487,f219])).
% 2.09/0.68  fof(f487,plain,(
% 2.09/0.68    ( ! [X0] : (sK3 != sK6(X0) | ~r2_hidden(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),X0) | k1_xboole_0 = X0) ) | ~spl7_8),
% 2.09/0.68    inference(superposition,[],[f114,f166])).
% 2.09/0.68  fof(f166,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl7_8),
% 2.09/0.68    inference(avatar_component_clause,[],[f164])).
% 2.09/0.68  fof(f114,plain,(
% 2.09/0.68    ( ! [X2,X0,X3,X1] : (k3_mcart_1(X0,X1,X2) != sK6(X3) | ~r2_hidden(k4_tarski(X0,X1),X3) | k1_xboole_0 = X3) )),
% 2.09/0.68    inference(superposition,[],[f55,f53])).
% 2.09/0.68  fof(f479,plain,(
% 2.09/0.68    spl7_13 | ~spl7_10),
% 2.09/0.68    inference(avatar_split_clause,[],[f474,f272,f476])).
% 2.09/0.68  fof(f474,plain,(
% 2.09/0.68    k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)) = sK6(k2_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)) | ~spl7_10),
% 2.09/0.68    inference(resolution,[],[f463,f61])).
% 2.09/0.68  fof(f463,plain,(
% 2.09/0.68    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_tarski(X0,sK3)) | sK6(k2_tarski(X0,sK3)) = X0) ) | ~spl7_10),
% 2.09/0.68    inference(equality_resolution,[],[f329])).
% 2.09/0.68  fof(f329,plain,(
% 2.09/0.68    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_tarski(X0,X1)) | sK6(k2_tarski(X0,X1)) = X0) ) | ~spl7_10),
% 2.09/0.68    inference(subsumption_resolution,[],[f328,f123])).
% 2.09/0.68  fof(f328,plain,(
% 2.09/0.68    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK6(k2_tarski(X0,X1)) = X0) ) | ~spl7_10),
% 2.09/0.68    inference(superposition,[],[f282,f219])).
% 2.09/0.68  fof(f282,plain,(
% 2.09/0.68    ( ! [X0] : (sK3 != sK6(X0) | ~r2_hidden(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),X0) | k1_xboole_0 = X0) ) | ~spl7_10),
% 2.09/0.68    inference(superposition,[],[f114,f274])).
% 2.09/0.68  fof(f274,plain,(
% 2.09/0.68    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl7_10),
% 2.09/0.68    inference(avatar_component_clause,[],[f272])).
% 2.09/0.68  fof(f98,plain,(
% 2.09/0.68    ~spl7_7),
% 2.09/0.68    inference(avatar_split_clause,[],[f31,f95])).
% 2.09/0.68  fof(f31,plain,(
% 2.09/0.68    k1_xboole_0 != sK0),
% 2.09/0.68    inference(cnf_transformation,[],[f16])).
% 2.09/0.68  fof(f16,plain,(
% 2.09/0.68    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 2.09/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15,f14])).
% 2.09/0.68  fof(f14,plain,(
% 2.09/0.68    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 2.09/0.68    introduced(choice_axiom,[])).
% 2.09/0.68  fof(f15,plain,(
% 2.09/0.68    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 2.09/0.68    introduced(choice_axiom,[])).
% 2.09/0.68  fof(f11,plain,(
% 2.09/0.68    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.09/0.68    inference(ennf_transformation,[],[f10])).
% 2.09/0.68  fof(f10,negated_conjecture,(
% 2.09/0.68    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.09/0.68    inference(negated_conjecture,[],[f9])).
% 2.09/0.68  fof(f9,conjecture,(
% 2.09/0.68    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.09/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 2.09/0.68  fof(f93,plain,(
% 2.09/0.68    ~spl7_6),
% 2.09/0.68    inference(avatar_split_clause,[],[f32,f90])).
% 2.09/0.68  fof(f32,plain,(
% 2.09/0.68    k1_xboole_0 != sK1),
% 2.09/0.68    inference(cnf_transformation,[],[f16])).
% 2.09/0.68  fof(f88,plain,(
% 2.09/0.68    ~spl7_5),
% 2.09/0.68    inference(avatar_split_clause,[],[f33,f85])).
% 2.09/0.68  fof(f33,plain,(
% 2.09/0.68    k1_xboole_0 != sK2),
% 2.09/0.68    inference(cnf_transformation,[],[f16])).
% 2.09/0.68  fof(f83,plain,(
% 2.09/0.68    spl7_4),
% 2.09/0.68    inference(avatar_split_clause,[],[f34,f80])).
% 2.09/0.68  fof(f34,plain,(
% 2.09/0.68    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.09/0.68    inference(cnf_transformation,[],[f16])).
% 2.09/0.68  fof(f78,plain,(
% 2.09/0.68    spl7_1 | spl7_2 | spl7_3),
% 2.09/0.68    inference(avatar_split_clause,[],[f35,f75,f71,f67])).
% 2.09/0.68  fof(f35,plain,(
% 2.09/0.68    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 2.09/0.68    inference(cnf_transformation,[],[f16])).
% 2.09/0.68  % SZS output end Proof for theBenchmark
% 2.09/0.68  % (32652)------------------------------
% 2.09/0.68  % (32652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.68  % (32652)Termination reason: Refutation
% 2.09/0.68  
% 2.09/0.68  % (32652)Memory used [KB]: 6908
% 2.09/0.68  % (32652)Time elapsed: 0.255 s
% 2.09/0.68  % (32652)------------------------------
% 2.09/0.68  % (32652)------------------------------
% 2.09/0.68  % (32630)Success in time 0.312 s
%------------------------------------------------------------------------------
