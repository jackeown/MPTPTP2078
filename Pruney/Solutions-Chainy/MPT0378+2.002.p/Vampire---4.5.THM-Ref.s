%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:34 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 251 expanded)
%              Number of leaves         :   35 ( 109 expanded)
%              Depth                    :   10
%              Number of atoms          :  526 (1403 expanded)
%              Number of equality atoms :   89 ( 221 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f887,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f167,f170,f180,f454,f457,f460,f463,f466,f469,f626,f680,f734,f886])).

fof(f886,plain,
    ( ~ spl12_9
    | ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f876])).

fof(f876,plain,
    ( $false
    | ~ spl12_9
    | ~ spl12_11 ),
    inference(resolution,[],[f863,f93])).

fof(f93,plain,(
    ! [X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( sP0(X6,X4,X3,X2,X1,X0)
    <=> ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f863,plain,
    ( ! [X0] : ~ sP0(X0,sK8,sK7,sK6,sK5,sK4)
    | ~ spl12_9
    | ~ spl12_11 ),
    inference(resolution,[],[f859,f327])).

fof(f327,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,k3_enumset1(X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(resolution,[],[f78,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP1(X0,X1,X2,X3,X4,X5) )
      & ( sP1(X0,X1,X2,X3,X4,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(definition_folding,[],[f22,f24,f23])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP1(X0,X1,X2,X3,X4,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5)
      | ~ sP0(X7,X4,X3,X2,X1,X0)
      | r2_hidden(X7,X5) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ( ( ~ sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5) )
          & ( sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f44,f45])).

fof(f45,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X6,X5) )
          & ( sP0(X6,X4,X3,X2,X1,X0)
            | r2_hidden(X6,X5) ) )
     => ( ( ~ sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5) )
        & ( sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ~ sP0(X6,X4,X3,X2,X1,X0) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f859,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | ~ spl12_9
    | ~ spl12_11 ),
    inference(resolution,[],[f794,f737])).

fof(f737,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl12_9 ),
    inference(resolution,[],[f162,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK9(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f162,plain,
    ( v1_xboole_0(sK2)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl12_9
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f794,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,k3_enumset1(sK4,sK5,sK6,sK7,sK8)) )
    | ~ spl12_11 ),
    inference(resolution,[],[f178,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f178,plain,
    ( m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl12_11
  <=> m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f734,plain,(
    ~ spl12_1 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | ~ spl12_1 ),
    inference(resolution,[],[f105,f59])).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f105,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl12_1
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f680,plain,
    ( spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f644,f107,f103])).

fof(f107,plain,
    ( spl12_2
  <=> r2_hidden(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f644,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f89,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f89,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2)) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f58,plain,(
    ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK8,sK2)
    & m1_subset_1(sK7,sK2)
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,sK2)
    & m1_subset_1(sK4,sK2)
    & m1_subset_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f31,f30,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(sK3,X2,X3,X4,X5,X6),k1_zfmisc_1(sK2))
                          & k1_xboole_0 != sK2
                          & m1_subset_1(X6,sK2) )
                      & m1_subset_1(X5,sK2) )
                  & m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,sK2) )
          & m1_subset_1(X2,sK2) )
      & m1_subset_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ m1_subset_1(k4_enumset1(sK3,X2,X3,X4,X5,X6),k1_zfmisc_1(sK2))
                        & k1_xboole_0 != sK2
                        & m1_subset_1(X6,sK2) )
                    & m1_subset_1(X5,sK2) )
                & m1_subset_1(X4,sK2) )
            & m1_subset_1(X3,sK2) )
        & m1_subset_1(X2,sK2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ m1_subset_1(k4_enumset1(sK3,sK4,X3,X4,X5,X6),k1_zfmisc_1(sK2))
                      & k1_xboole_0 != sK2
                      & m1_subset_1(X6,sK2) )
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,sK2) )
          & m1_subset_1(X3,sK2) )
      & m1_subset_1(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ m1_subset_1(k4_enumset1(sK3,sK4,X3,X4,X5,X6),k1_zfmisc_1(sK2))
                    & k1_xboole_0 != sK2
                    & m1_subset_1(X6,sK2) )
                & m1_subset_1(X5,sK2) )
            & m1_subset_1(X4,sK2) )
        & m1_subset_1(X3,sK2) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,X4,X5,X6),k1_zfmisc_1(sK2))
                  & k1_xboole_0 != sK2
                  & m1_subset_1(X6,sK2) )
              & m1_subset_1(X5,sK2) )
          & m1_subset_1(X4,sK2) )
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,X4,X5,X6),k1_zfmisc_1(sK2))
                & k1_xboole_0 != sK2
                & m1_subset_1(X6,sK2) )
            & m1_subset_1(X5,sK2) )
        & m1_subset_1(X4,sK2) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,X5,X6),k1_zfmisc_1(sK2))
              & k1_xboole_0 != sK2
              & m1_subset_1(X6,sK2) )
          & m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,X5,X6),k1_zfmisc_1(sK2))
            & k1_xboole_0 != sK2
            & m1_subset_1(X6,sK2) )
        & m1_subset_1(X5,sK2) )
   => ( ? [X6] :
          ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,X6),k1_zfmisc_1(sK2))
          & k1_xboole_0 != sK2
          & m1_subset_1(X6,sK2) )
      & m1_subset_1(sK7,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X6] :
        ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,X6),k1_zfmisc_1(sK2))
        & k1_xboole_0 != sK2
        & m1_subset_1(X6,sK2) )
   => ( ~ m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK8,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_subset_1)).

fof(f626,plain,(
    ~ spl12_44 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | ~ spl12_44 ),
    inference(trivial_inequality_removal,[],[f624])).

fof(f624,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl12_44 ),
    inference(superposition,[],[f57,f453])).

fof(f453,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_44 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl12_44
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f469,plain,(
    spl12_43 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl12_43 ),
    inference(resolution,[],[f449,f56])).

fof(f56,plain,(
    m1_subset_1(sK8,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f449,plain,
    ( ~ m1_subset_1(sK8,sK2)
    | spl12_43 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl12_43
  <=> m1_subset_1(sK8,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).

fof(f466,plain,(
    spl12_42 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | spl12_42 ),
    inference(resolution,[],[f445,f55])).

fof(f55,plain,(
    m1_subset_1(sK7,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f445,plain,
    ( ~ m1_subset_1(sK7,sK2)
    | spl12_42 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl12_42
  <=> m1_subset_1(sK7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f463,plain,(
    spl12_41 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | spl12_41 ),
    inference(resolution,[],[f441,f54])).

fof(f54,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f441,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | spl12_41 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl12_41
  <=> m1_subset_1(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).

fof(f460,plain,(
    spl12_40 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | spl12_40 ),
    inference(resolution,[],[f437,f53])).

fof(f53,plain,(
    m1_subset_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f437,plain,
    ( ~ m1_subset_1(sK5,sK2)
    | spl12_40 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl12_40
  <=> m1_subset_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).

fof(f457,plain,(
    spl12_39 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl12_39 ),
    inference(resolution,[],[f433,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f433,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | spl12_39 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl12_39
  <=> m1_subset_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f454,plain,
    ( ~ spl12_39
    | ~ spl12_40
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_43
    | spl12_44
    | spl12_11 ),
    inference(avatar_split_clause,[],[f428,f177,f451,f447,f443,f439,f435,f431])).

fof(f428,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK8,sK2)
    | ~ m1_subset_1(sK7,sK2)
    | ~ m1_subset_1(sK6,sK2)
    | ~ m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK4,sK2)
    | spl12_11 ),
    inference(resolution,[],[f66,f179])).

fof(f179,plain,
    ( ~ m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))
    | spl12_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ( k1_xboole_0 != X0
                       => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_subset_1)).

fof(f180,plain,
    ( spl12_1
    | ~ spl12_11
    | spl12_8 ),
    inference(avatar_split_clause,[],[f175,f151,f177,f103])).

fof(f151,plain,
    ( spl12_8
  <=> r1_tarski(k3_enumset1(sK4,sK5,sK6,sK7,sK8),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f175,plain,
    ( ~ m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | spl12_8 ),
    inference(resolution,[],[f172,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f172,plain,
    ( ~ r2_hidden(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))
    | spl12_8 ),
    inference(resolution,[],[f153,f92])).

fof(f92,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK10(X0,X1),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r1_tarski(sK10(X0,X1),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK10(X0,X1),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( r1_tarski(sK10(X0,X1),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f153,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK5,sK6,sK7,sK8),sK2)
    | spl12_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f170,plain,(
    spl12_10 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl12_10 ),
    inference(resolution,[],[f166,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f166,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl12_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl12_10
  <=> m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f167,plain,
    ( spl12_9
    | ~ spl12_10
    | spl12_7 ),
    inference(avatar_split_clause,[],[f158,f147,f164,f160])).

fof(f147,plain,
    ( spl12_7
  <=> r1_tarski(k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f158,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | spl12_7 ),
    inference(resolution,[],[f155,f62])).

fof(f155,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl12_7 ),
    inference(resolution,[],[f149,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f149,plain,
    ( ~ r1_tarski(k1_tarski(sK3),sK2)
    | spl12_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f154,plain,
    ( ~ spl12_7
    | ~ spl12_8
    | spl12_2 ),
    inference(avatar_split_clause,[],[f145,f107,f151,f147])).

fof(f145,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK5,sK6,sK7,sK8),sK2)
    | ~ r1_tarski(k1_tarski(sK3),sK2)
    | spl12_2 ),
    inference(resolution,[],[f74,f111])).

fof(f111,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),sK2)
    | spl12_2 ),
    inference(resolution,[],[f109,f91])).

fof(f91,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2))
    | spl12_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (21405)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.48  % (21403)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.49  % (21401)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (21422)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (21409)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (21426)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (21425)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (21400)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (21422)Refutation not found, incomplete strategy% (21422)------------------------------
% 0.20/0.51  % (21422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21422)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21422)Memory used [KB]: 10746
% 0.20/0.51  % (21422)Time elapsed: 0.103 s
% 0.20/0.51  % (21422)------------------------------
% 0.20/0.51  % (21422)------------------------------
% 0.20/0.51  % (21406)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (21410)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (21423)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (21404)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (21411)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (21421)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (21417)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (21415)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (21429)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (21402)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (21414)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (21420)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (21412)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (21407)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (21428)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (21427)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (21413)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (21402)Refutation not found, incomplete strategy% (21402)------------------------------
% 0.20/0.53  % (21402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21402)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (21402)Memory used [KB]: 10746
% 0.20/0.53  % (21402)Time elapsed: 0.129 s
% 0.20/0.53  % (21402)------------------------------
% 0.20/0.53  % (21402)------------------------------
% 0.20/0.54  % (21424)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (21416)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (21408)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (21418)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (21408)Refutation not found, incomplete strategy% (21408)------------------------------
% 0.20/0.54  % (21408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21419)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.55  % (21408)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (21408)Memory used [KB]: 10746
% 1.46/0.55  % (21408)Time elapsed: 0.143 s
% 1.46/0.55  % (21408)------------------------------
% 1.46/0.55  % (21408)------------------------------
% 1.58/0.57  % (21412)Refutation found. Thanks to Tanya!
% 1.58/0.57  % SZS status Theorem for theBenchmark
% 1.58/0.59  % SZS output start Proof for theBenchmark
% 1.58/0.59  fof(f887,plain,(
% 1.58/0.59    $false),
% 1.58/0.59    inference(avatar_sat_refutation,[],[f154,f167,f170,f180,f454,f457,f460,f463,f466,f469,f626,f680,f734,f886])).
% 1.58/0.60  fof(f886,plain,(
% 1.58/0.60    ~spl12_9 | ~spl12_11),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f876])).
% 1.58/0.60  fof(f876,plain,(
% 1.58/0.60    $false | (~spl12_9 | ~spl12_11)),
% 1.58/0.60    inference(resolution,[],[f863,f93])).
% 1.58/0.60  fof(f93,plain,(
% 1.58/0.60    ( ! [X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5)) )),
% 1.58/0.60    inference(equality_resolution,[],[f86])).
% 1.58/0.60  fof(f86,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5) | X0 != X1) )),
% 1.58/0.60    inference(cnf_transformation,[],[f49])).
% 1.58/0.60  fof(f49,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 1.58/0.60    inference(rectify,[],[f48])).
% 1.58/0.60  fof(f48,plain,(
% 1.58/0.60    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 1.58/0.60    inference(flattening,[],[f47])).
% 1.58/0.60  fof(f47,plain,(
% 1.58/0.60    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 1.58/0.60    inference(nnf_transformation,[],[f23])).
% 1.58/0.60  fof(f23,plain,(
% 1.58/0.60    ! [X6,X4,X3,X2,X1,X0] : (sP0(X6,X4,X3,X2,X1,X0) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6))),
% 1.58/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.58/0.60  fof(f863,plain,(
% 1.58/0.60    ( ! [X0] : (~sP0(X0,sK8,sK7,sK6,sK5,sK4)) ) | (~spl12_9 | ~spl12_11)),
% 1.58/0.60    inference(resolution,[],[f859,f327])).
% 1.58/0.60  fof(f327,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X0,k3_enumset1(X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 1.58/0.60    inference(resolution,[],[f78,f98])).
% 1.58/0.60  fof(f98,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.58/0.60    inference(equality_resolution,[],[f87])).
% 1.58/0.60  fof(f87,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.58/0.60    inference(cnf_transformation,[],[f50])).
% 1.58/0.60  fof(f50,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP1(X0,X1,X2,X3,X4,X5)) & (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.58/0.60    inference(nnf_transformation,[],[f25])).
% 1.58/0.60  fof(f25,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP1(X0,X1,X2,X3,X4,X5))),
% 1.58/0.60    inference(definition_folding,[],[f22,f24,f23])).
% 1.58/0.60  fof(f24,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : (sP1(X0,X1,X2,X3,X4,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> sP0(X6,X4,X3,X2,X1,X0)))),
% 1.58/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.58/0.60  fof(f22,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.58/0.60    inference(ennf_transformation,[],[f8])).
% 1.58/0.60  fof(f8,axiom,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 1.58/0.60  fof(f78,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5) | ~sP0(X7,X4,X3,X2,X1,X0) | r2_hidden(X7,X5)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f46])).
% 1.58/0.60  fof(f46,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ((~sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f44,f45])).
% 1.58/0.60  fof(f45,plain,(
% 1.58/0.60    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5))) => ((~sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK11(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK11(X0,X1,X2,X3,X4,X5),X5))))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f44,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.58/0.60    inference(rectify,[],[f43])).
% 1.58/0.60  fof(f43,plain,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | ~sP0(X6,X4,X3,X2,X1,X0)) & (sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.58/0.60    inference(nnf_transformation,[],[f24])).
% 1.58/0.60  fof(f859,plain,(
% 1.58/0.60    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ) | (~spl12_9 | ~spl12_11)),
% 1.58/0.60    inference(resolution,[],[f794,f737])).
% 1.58/0.60  fof(f737,plain,(
% 1.58/0.60    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | ~spl12_9),
% 1.58/0.60    inference(resolution,[],[f162,f60])).
% 1.58/0.60  fof(f60,plain,(
% 1.58/0.60    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f36])).
% 1.58/0.60  fof(f36,plain,(
% 1.58/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f35])).
% 1.58/0.60  fof(f35,plain,(
% 1.58/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f34,plain,(
% 1.58/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.58/0.60    inference(rectify,[],[f33])).
% 1.58/0.60  fof(f33,plain,(
% 1.58/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.58/0.60    inference(nnf_transformation,[],[f1])).
% 1.58/0.60  fof(f1,axiom,(
% 1.58/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.58/0.60  fof(f162,plain,(
% 1.58/0.60    v1_xboole_0(sK2) | ~spl12_9),
% 1.58/0.60    inference(avatar_component_clause,[],[f160])).
% 1.58/0.60  fof(f160,plain,(
% 1.58/0.60    spl12_9 <=> v1_xboole_0(sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.58/0.60  fof(f794,plain,(
% 1.58/0.60    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ) | ~spl12_11),
% 1.58/0.60    inference(resolution,[],[f178,f67])).
% 1.58/0.60  fof(f67,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f19])).
% 1.58/0.60  fof(f19,plain,(
% 1.58/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.58/0.60    inference(ennf_transformation,[],[f10])).
% 1.58/0.60  fof(f10,axiom,(
% 1.58/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.58/0.60  fof(f178,plain,(
% 1.58/0.60    m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) | ~spl12_11),
% 1.58/0.60    inference(avatar_component_clause,[],[f177])).
% 1.58/0.60  fof(f177,plain,(
% 1.58/0.60    spl12_11 <=> m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.58/0.60  fof(f734,plain,(
% 1.58/0.60    ~spl12_1),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f730])).
% 1.58/0.60  fof(f730,plain,(
% 1.58/0.60    $false | ~spl12_1),
% 1.58/0.60    inference(resolution,[],[f105,f59])).
% 1.58/0.60  fof(f59,plain,(
% 1.58/0.60    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f9])).
% 1.58/0.60  fof(f9,axiom,(
% 1.58/0.60    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.58/0.60  fof(f105,plain,(
% 1.58/0.60    v1_xboole_0(k1_zfmisc_1(sK2)) | ~spl12_1),
% 1.58/0.60    inference(avatar_component_clause,[],[f103])).
% 1.58/0.60  fof(f103,plain,(
% 1.58/0.60    spl12_1 <=> v1_xboole_0(k1_zfmisc_1(sK2))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.58/0.60  fof(f680,plain,(
% 1.58/0.60    spl12_1 | ~spl12_2),
% 1.58/0.60    inference(avatar_split_clause,[],[f644,f107,f103])).
% 1.58/0.60  fof(f107,plain,(
% 1.58/0.60    spl12_2 <=> r2_hidden(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.58/0.60  fof(f644,plain,(
% 1.58/0.60    ~r2_hidden(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2))),
% 1.58/0.60    inference(resolution,[],[f89,f63])).
% 1.58/0.60  fof(f63,plain,(
% 1.58/0.60    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f37])).
% 1.58/0.60  fof(f37,plain,(
% 1.58/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.58/0.60    inference(nnf_transformation,[],[f16])).
% 1.58/0.60  fof(f16,plain,(
% 1.58/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.58/0.60    inference(ennf_transformation,[],[f7])).
% 1.58/0.60  fof(f7,axiom,(
% 1.58/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.58/0.60  fof(f89,plain,(
% 1.58/0.60    ~m1_subset_1(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2))),
% 1.58/0.60    inference(definition_unfolding,[],[f58,f75])).
% 1.58/0.60  fof(f75,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f3])).
% 1.58/0.60  fof(f3,axiom,(
% 1.58/0.60    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 1.58/0.60  fof(f58,plain,(
% 1.58/0.60    ~m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2))),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f32,plain,(
% 1.58/0.60    (((((~m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK8,sK2)) & m1_subset_1(sK7,sK2)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,sK2)) & m1_subset_1(sK4,sK2)) & m1_subset_1(sK3,sK2)),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f31,f30,f29,f28,f27,f26])).
% 1.58/0.60  fof(f26,plain,(
% 1.58/0.60    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,X2,X3,X4,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(X2,sK2)) & m1_subset_1(sK3,sK2))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f27,plain,(
% 1.58/0.60    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,X2,X3,X4,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(X2,sK2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,X3,X4,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) & m1_subset_1(sK4,sK2))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f28,plain,(
% 1.58/0.60    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,X3,X4,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(X3,sK2)) => (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,sK5,X4,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) & m1_subset_1(sK5,sK2))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f29,plain,(
% 1.58/0.60    ? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,sK5,X4,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,sK2)) => (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) & m1_subset_1(sK6,sK2))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f30,plain,(
% 1.58/0.60    ? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,X5,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(X5,sK2)) => (? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) & m1_subset_1(sK7,sK2))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f31,plain,(
% 1.58/0.60    ? [X6] : (~m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,X6),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(X6,sK2)) => (~m1_subset_1(k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK8,sK2))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f15,plain,(
% 1.58/0.60    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.58/0.60    inference(flattening,[],[f14])).
% 1.58/0.60  fof(f14,plain,(
% 1.58/0.60    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 1.58/0.60    inference(ennf_transformation,[],[f13])).
% 1.58/0.60  fof(f13,negated_conjecture,(
% 1.58/0.60    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 1.58/0.60    inference(negated_conjecture,[],[f12])).
% 1.58/0.60  fof(f12,conjecture,(
% 1.58/0.60    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_subset_1)).
% 1.58/0.60  fof(f626,plain,(
% 1.58/0.60    ~spl12_44),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f625])).
% 1.58/0.60  fof(f625,plain,(
% 1.58/0.60    $false | ~spl12_44),
% 1.58/0.60    inference(trivial_inequality_removal,[],[f624])).
% 1.58/0.60  fof(f624,plain,(
% 1.58/0.60    k1_xboole_0 != k1_xboole_0 | ~spl12_44),
% 1.58/0.60    inference(superposition,[],[f57,f453])).
% 1.58/0.60  fof(f453,plain,(
% 1.58/0.60    k1_xboole_0 = sK2 | ~spl12_44),
% 1.58/0.60    inference(avatar_component_clause,[],[f451])).
% 1.58/0.60  fof(f451,plain,(
% 1.58/0.60    spl12_44 <=> k1_xboole_0 = sK2),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).
% 1.58/0.60  fof(f57,plain,(
% 1.58/0.60    k1_xboole_0 != sK2),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f469,plain,(
% 1.58/0.60    spl12_43),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f467])).
% 1.58/0.60  fof(f467,plain,(
% 1.58/0.60    $false | spl12_43),
% 1.58/0.60    inference(resolution,[],[f449,f56])).
% 1.58/0.60  fof(f56,plain,(
% 1.58/0.60    m1_subset_1(sK8,sK2)),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f449,plain,(
% 1.58/0.60    ~m1_subset_1(sK8,sK2) | spl12_43),
% 1.58/0.60    inference(avatar_component_clause,[],[f447])).
% 1.58/0.60  fof(f447,plain,(
% 1.58/0.60    spl12_43 <=> m1_subset_1(sK8,sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).
% 1.58/0.60  fof(f466,plain,(
% 1.58/0.60    spl12_42),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f464])).
% 1.58/0.60  fof(f464,plain,(
% 1.58/0.60    $false | spl12_42),
% 1.58/0.60    inference(resolution,[],[f445,f55])).
% 1.58/0.60  fof(f55,plain,(
% 1.58/0.60    m1_subset_1(sK7,sK2)),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f445,plain,(
% 1.58/0.60    ~m1_subset_1(sK7,sK2) | spl12_42),
% 1.58/0.60    inference(avatar_component_clause,[],[f443])).
% 1.58/0.60  fof(f443,plain,(
% 1.58/0.60    spl12_42 <=> m1_subset_1(sK7,sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).
% 1.58/0.60  fof(f463,plain,(
% 1.58/0.60    spl12_41),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f461])).
% 1.58/0.60  fof(f461,plain,(
% 1.58/0.60    $false | spl12_41),
% 1.58/0.60    inference(resolution,[],[f441,f54])).
% 1.58/0.60  fof(f54,plain,(
% 1.58/0.60    m1_subset_1(sK6,sK2)),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f441,plain,(
% 1.58/0.60    ~m1_subset_1(sK6,sK2) | spl12_41),
% 1.58/0.60    inference(avatar_component_clause,[],[f439])).
% 1.58/0.60  fof(f439,plain,(
% 1.58/0.60    spl12_41 <=> m1_subset_1(sK6,sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).
% 1.58/0.60  fof(f460,plain,(
% 1.58/0.60    spl12_40),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f458])).
% 1.58/0.60  fof(f458,plain,(
% 1.58/0.60    $false | spl12_40),
% 1.58/0.60    inference(resolution,[],[f437,f53])).
% 1.58/0.60  fof(f53,plain,(
% 1.58/0.60    m1_subset_1(sK5,sK2)),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f437,plain,(
% 1.58/0.60    ~m1_subset_1(sK5,sK2) | spl12_40),
% 1.58/0.60    inference(avatar_component_clause,[],[f435])).
% 1.58/0.60  fof(f435,plain,(
% 1.58/0.60    spl12_40 <=> m1_subset_1(sK5,sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).
% 1.58/0.60  fof(f457,plain,(
% 1.58/0.60    spl12_39),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f455])).
% 1.58/0.60  fof(f455,plain,(
% 1.58/0.60    $false | spl12_39),
% 1.58/0.60    inference(resolution,[],[f433,f52])).
% 1.58/0.60  fof(f52,plain,(
% 1.58/0.60    m1_subset_1(sK4,sK2)),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f433,plain,(
% 1.58/0.60    ~m1_subset_1(sK4,sK2) | spl12_39),
% 1.58/0.60    inference(avatar_component_clause,[],[f431])).
% 1.58/0.60  fof(f431,plain,(
% 1.58/0.60    spl12_39 <=> m1_subset_1(sK4,sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).
% 1.58/0.60  fof(f454,plain,(
% 1.58/0.60    ~spl12_39 | ~spl12_40 | ~spl12_41 | ~spl12_42 | ~spl12_43 | spl12_44 | spl12_11),
% 1.58/0.60    inference(avatar_split_clause,[],[f428,f177,f451,f447,f443,f439,f435,f431])).
% 1.58/0.60  fof(f428,plain,(
% 1.58/0.60    k1_xboole_0 = sK2 | ~m1_subset_1(sK8,sK2) | ~m1_subset_1(sK7,sK2) | ~m1_subset_1(sK6,sK2) | ~m1_subset_1(sK5,sK2) | ~m1_subset_1(sK4,sK2) | spl12_11),
% 1.58/0.60    inference(resolution,[],[f66,f179])).
% 1.58/0.60  fof(f179,plain,(
% 1.58/0.60    ~m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) | spl12_11),
% 1.58/0.60    inference(avatar_component_clause,[],[f177])).
% 1.58/0.60  fof(f66,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f18])).
% 1.58/0.60  fof(f18,plain,(
% 1.58/0.60    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.58/0.60    inference(flattening,[],[f17])).
% 1.58/0.60  fof(f17,plain,(
% 1.58/0.60    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.58/0.60    inference(ennf_transformation,[],[f11])).
% 1.58/0.60  fof(f11,axiom,(
% 1.58/0.60    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => (k1_xboole_0 != X0 => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))))))))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_subset_1)).
% 1.58/0.60  fof(f180,plain,(
% 1.58/0.60    spl12_1 | ~spl12_11 | spl12_8),
% 1.58/0.60    inference(avatar_split_clause,[],[f175,f151,f177,f103])).
% 1.58/0.60  fof(f151,plain,(
% 1.58/0.60    spl12_8 <=> r1_tarski(k3_enumset1(sK4,sK5,sK6,sK7,sK8),sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.58/0.60  fof(f175,plain,(
% 1.58/0.60    ~m1_subset_1(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) | spl12_8),
% 1.58/0.60    inference(resolution,[],[f172,f62])).
% 1.58/0.60  fof(f62,plain,(
% 1.58/0.60    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f37])).
% 1.58/0.60  fof(f172,plain,(
% 1.58/0.60    ~r2_hidden(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK2)) | spl12_8),
% 1.58/0.60    inference(resolution,[],[f153,f92])).
% 1.58/0.60  fof(f92,plain,(
% 1.58/0.60    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.58/0.60    inference(equality_resolution,[],[f68])).
% 1.58/0.60  fof(f68,plain,(
% 1.58/0.60    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.58/0.60    inference(cnf_transformation,[],[f41])).
% 1.58/0.60  fof(f41,plain,(
% 1.58/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK10(X0,X1),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r1_tarski(sK10(X0,X1),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f39,f40])).
% 1.58/0.60  fof(f40,plain,(
% 1.58/0.60    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK10(X0,X1),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r1_tarski(sK10(X0,X1),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f39,plain,(
% 1.58/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.58/0.60    inference(rectify,[],[f38])).
% 1.58/0.60  fof(f38,plain,(
% 1.58/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.58/0.60    inference(nnf_transformation,[],[f5])).
% 1.58/0.60  fof(f5,axiom,(
% 1.58/0.60    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.58/0.60  fof(f153,plain,(
% 1.58/0.60    ~r1_tarski(k3_enumset1(sK4,sK5,sK6,sK7,sK8),sK2) | spl12_8),
% 1.58/0.60    inference(avatar_component_clause,[],[f151])).
% 1.58/0.60  fof(f170,plain,(
% 1.58/0.60    spl12_10),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f168])).
% 1.58/0.60  fof(f168,plain,(
% 1.58/0.60    $false | spl12_10),
% 1.58/0.60    inference(resolution,[],[f166,f51])).
% 1.58/0.60  fof(f51,plain,(
% 1.58/0.60    m1_subset_1(sK3,sK2)),
% 1.58/0.60    inference(cnf_transformation,[],[f32])).
% 1.58/0.60  fof(f166,plain,(
% 1.58/0.60    ~m1_subset_1(sK3,sK2) | spl12_10),
% 1.58/0.60    inference(avatar_component_clause,[],[f164])).
% 1.58/0.60  fof(f164,plain,(
% 1.58/0.60    spl12_10 <=> m1_subset_1(sK3,sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.58/0.60  fof(f167,plain,(
% 1.58/0.60    spl12_9 | ~spl12_10 | spl12_7),
% 1.58/0.60    inference(avatar_split_clause,[],[f158,f147,f164,f160])).
% 1.58/0.60  fof(f147,plain,(
% 1.58/0.60    spl12_7 <=> r1_tarski(k1_tarski(sK3),sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.58/0.60  fof(f158,plain,(
% 1.58/0.60    ~m1_subset_1(sK3,sK2) | v1_xboole_0(sK2) | spl12_7),
% 1.58/0.60    inference(resolution,[],[f155,f62])).
% 1.58/0.60  fof(f155,plain,(
% 1.58/0.60    ~r2_hidden(sK3,sK2) | spl12_7),
% 1.58/0.60    inference(resolution,[],[f149,f73])).
% 1.58/0.60  fof(f73,plain,(
% 1.58/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f42])).
% 1.58/0.60  fof(f42,plain,(
% 1.58/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.58/0.60    inference(nnf_transformation,[],[f6])).
% 1.58/0.60  fof(f6,axiom,(
% 1.58/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 1.58/0.60  fof(f149,plain,(
% 1.58/0.60    ~r1_tarski(k1_tarski(sK3),sK2) | spl12_7),
% 1.58/0.60    inference(avatar_component_clause,[],[f147])).
% 1.58/0.60  fof(f154,plain,(
% 1.58/0.60    ~spl12_7 | ~spl12_8 | spl12_2),
% 1.58/0.60    inference(avatar_split_clause,[],[f145,f107,f151,f147])).
% 1.58/0.60  fof(f145,plain,(
% 1.58/0.60    ~r1_tarski(k3_enumset1(sK4,sK5,sK6,sK7,sK8),sK2) | ~r1_tarski(k1_tarski(sK3),sK2) | spl12_2),
% 1.58/0.60    inference(resolution,[],[f74,f111])).
% 1.58/0.60  fof(f111,plain,(
% 1.58/0.60    ~r1_tarski(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),sK2) | spl12_2),
% 1.58/0.60    inference(resolution,[],[f109,f91])).
% 1.58/0.60  fof(f91,plain,(
% 1.58/0.60    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.58/0.60    inference(equality_resolution,[],[f69])).
% 1.58/0.60  fof(f69,plain,(
% 1.58/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.58/0.60    inference(cnf_transformation,[],[f41])).
% 1.58/0.60  fof(f109,plain,(
% 1.58/0.60    ~r2_hidden(k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK2)) | spl12_2),
% 1.58/0.60    inference(avatar_component_clause,[],[f107])).
% 1.58/0.60  fof(f74,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f21])).
% 1.58/0.60  fof(f21,plain,(
% 1.58/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.58/0.60    inference(flattening,[],[f20])).
% 1.58/0.60  fof(f20,plain,(
% 1.58/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.58/0.60    inference(ennf_transformation,[],[f2])).
% 1.58/0.60  fof(f2,axiom,(
% 1.58/0.60    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.58/0.60  % SZS output end Proof for theBenchmark
% 1.58/0.60  % (21412)------------------------------
% 1.58/0.60  % (21412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (21412)Termination reason: Refutation
% 1.58/0.60  
% 1.58/0.60  % (21412)Memory used [KB]: 6652
% 1.58/0.60  % (21412)Time elapsed: 0.163 s
% 1.58/0.60  % (21412)------------------------------
% 1.58/0.60  % (21412)------------------------------
% 1.58/0.60  % (21398)Success in time 0.244 s
%------------------------------------------------------------------------------
