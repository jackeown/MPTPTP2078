%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 409 expanded)
%              Number of leaves         :   32 ( 123 expanded)
%              Depth                    :   18
%              Number of atoms          :  633 (2505 expanded)
%              Number of equality atoms :  254 (1292 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f199,f213,f221,f229,f237,f240,f392,f398,f410,f418,f424,f430])).

fof(f430,plain,(
    ~ spl12_7 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f428,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X5
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X5
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f428,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f425,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f425,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl12_7 ),
    inference(resolution,[],[f379,f90])).

fof(f90,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f48,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f379,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9 )
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl12_7
  <=> ! [X9,X8] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f424,plain,(
    ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f422,f52])).

fof(f52,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f422,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f419,f51])).

fof(f419,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl12_11 ),
    inference(resolution,[],[f391,f90])).

fof(f391,plain,
    ( ! [X0,X3] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X3 )
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl12_11
  <=> ! [X3,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
        | k1_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f418,plain,(
    ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f416,f52])).

fof(f416,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f413,f50])).

fof(f413,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl12_10 ),
    inference(resolution,[],[f388,f90])).

fof(f388,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1 )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl12_10
  <=> ! [X1,X2] :
        ( k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f410,plain,
    ( ~ spl12_1
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_9 ),
    inference(resolution,[],[f400,f118])).

fof(f118,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl12_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f400,plain,
    ( ! [X6,X4,X5] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
    | ~ spl12_9 ),
    inference(resolution,[],[f385,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f385,plain,
    ( ! [X4,X5] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl12_9
  <=> ! [X5,X4] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f398,plain,
    ( ~ spl12_1
    | ~ spl12_8 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_8 ),
    inference(resolution,[],[f382,f118])).

fof(f382,plain,
    ( ! [X6,X7] : ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl12_8
  <=> ! [X7,X6] : ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f392,plain,
    ( spl12_7
    | spl12_8
    | spl12_9
    | spl12_10
    | spl12_11 ),
    inference(avatar_split_clause,[],[f376,f390,f387,f384,f381,f378])).

fof(f376,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8 ) ),
    inference(subsumption_resolution,[],[f375,f350])).

fof(f350,plain,(
    sK3 != k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f349,f50])).

fof(f349,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f348,f51])).

fof(f348,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f347,f52])).

fof(f347,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f342,f90])).

fof(f342,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f53,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f65])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f53,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f375,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | sK3 = k1_mcart_1(k1_mcart_1(sK4))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8 ) ),
    inference(equality_resolution,[],[f365])).

fof(f365,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sK4 != X4
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | sK3 = k1_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X4,k2_zfmisc_1(X7,X8))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2))
      | k1_xboole_0 = X10
      | k1_xboole_0 = X9 ) ),
    inference(subsumption_resolution,[],[f363,f52])).

fof(f363,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | sK3 = k1_mcart_1(k1_mcart_1(X4))
      | sK4 != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X4,k2_zfmisc_1(X7,X8))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X10
      | k1_xboole_0 = X9 ) ),
    inference(resolution,[],[f361,f304])).

fof(f304,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(X7),X6)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(X7),X6)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f94,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f65])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f80,f65])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f361,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | sK4 != X0
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X0,k2_zfmisc_1(X7,X8)) ) ),
    inference(superposition,[],[f355,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f62,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f355,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sK4 != k4_tarski(k1_mcart_1(X0),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(X5,sK2)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7)) ) ),
    inference(subsumption_resolution,[],[f352,f50])).

fof(f352,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(X5,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X5)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7)) ) ),
    inference(resolution,[],[f345,f337])).

fof(f337,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(X3,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X3)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5)) ) ),
    inference(subsumption_resolution,[],[f335,f51])).

fof(f335,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X1
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(X3,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X3)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5)) ) ),
    inference(resolution,[],[f332,f181])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | k1_mcart_1(X0) = sK3
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f89,f179])).

fof(f89,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X5
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f49,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X5
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f332,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f95,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f65])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f81,f65])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f345,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f96,f93])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f82,f65])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f240,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f239,f120,f116])).

fof(f120,plain,
    ( spl12_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f239,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f90,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f237,plain,(
    ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f231,f51])).

fof(f231,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_6 ),
    inference(resolution,[],[f212,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f212,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl12_6
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f229,plain,(
    ~ spl12_5 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f223,f50])).

fof(f223,plain,
    ( k1_xboole_0 = sK0
    | ~ spl12_5 ),
    inference(resolution,[],[f209,f57])).

fof(f209,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl12_5
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f221,plain,(
    ~ spl12_4 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f215,f52])).

fof(f215,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_4 ),
    inference(resolution,[],[f198,f57])).

fof(f198,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl12_4
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f213,plain,
    ( spl12_5
    | spl12_6
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f200,f194,f211,f208])).

fof(f194,plain,
    ( spl12_3
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl12_3 ),
    inference(resolution,[],[f195,f103])).

fof(f103,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
              & r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
                & r2_hidden(sK11(X0,X1,X8),X1)
                & r2_hidden(sK10(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f41,f44,f43,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
        & r2_hidden(sK11(X0,X1,X8),X1)
        & r2_hidden(sK10(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

% (5244)Termination reason: Refutation not found, incomplete strategy

% (5244)Memory used [KB]: 10874
% (5244)Time elapsed: 0.168 s
% (5244)------------------------------
% (5244)------------------------------
fof(f195,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f194])).

fof(f199,plain,
    ( spl12_3
    | spl12_4
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f192,f120,f197,f194])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f189,f137])).

fof(f137,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f130,f132])).

fof(f132,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f130,f57])).

fof(f130,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f129,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f66,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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

fof(f189,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK2)
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl12_2 ),
    inference(superposition,[],[f103,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl12_2 ),
    inference(resolution,[],[f122,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f57,f55])).

fof(f122,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (5225)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (5225)Refutation not found, incomplete strategy% (5225)------------------------------
% 0.22/0.51  % (5225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5242)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (5225)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (5225)Memory used [KB]: 10746
% 0.22/0.51  % (5225)Time elapsed: 0.091 s
% 0.22/0.51  % (5225)------------------------------
% 0.22/0.51  % (5225)------------------------------
% 0.22/0.52  % (5228)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (5226)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (5239)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (5237)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (5247)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (5223)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (5227)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (5250)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (5224)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (5229)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (5227)Refutation not found, incomplete strategy% (5227)------------------------------
% 0.22/0.54  % (5227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5227)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5227)Memory used [KB]: 6268
% 0.22/0.54  % (5227)Time elapsed: 0.125 s
% 0.22/0.54  % (5227)------------------------------
% 0.22/0.54  % (5227)------------------------------
% 0.22/0.54  % (5252)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (5254)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (5240)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (5248)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (5245)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (5249)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (5236)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (5246)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (5253)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (5245)Refutation not found, incomplete strategy% (5245)------------------------------
% 0.22/0.55  % (5245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5246)Refutation not found, incomplete strategy% (5246)------------------------------
% 0.22/0.55  % (5246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5246)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5246)Memory used [KB]: 10874
% 0.22/0.55  % (5246)Time elapsed: 0.137 s
% 0.22/0.55  % (5246)------------------------------
% 0.22/0.55  % (5246)------------------------------
% 0.22/0.55  % (5241)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (5243)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (5235)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (5232)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (5233)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (5238)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (5230)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (5232)Refutation not found, incomplete strategy% (5232)------------------------------
% 0.22/0.56  % (5232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (5245)Memory used [KB]: 1791
% 0.22/0.56  % (5245)Time elapsed: 0.141 s
% 0.22/0.56  % (5245)------------------------------
% 0.22/0.56  % (5245)------------------------------
% 0.22/0.56  % (5232)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (5232)Memory used [KB]: 10746
% 0.22/0.56  % (5232)Time elapsed: 0.157 s
% 0.22/0.56  % (5232)------------------------------
% 0.22/0.56  % (5232)------------------------------
% 0.22/0.57  % (5244)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (5244)Refutation not found, incomplete strategy% (5244)------------------------------
% 0.22/0.57  % (5244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (5234)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (5226)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (5234)Refutation not found, incomplete strategy% (5234)------------------------------
% 0.22/0.58  % (5234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (5234)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (5234)Memory used [KB]: 10618
% 0.22/0.58  % (5234)Time elapsed: 0.166 s
% 0.22/0.58  % (5234)------------------------------
% 0.22/0.58  % (5234)------------------------------
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f431,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f199,f213,f221,f229,f237,f240,f392,f398,f410,f418,f424,f430])).
% 0.22/0.59  fof(f430,plain,(
% 0.22/0.59    ~spl12_7),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f429])).
% 0.22/0.59  fof(f429,plain,(
% 0.22/0.59    $false | ~spl12_7),
% 0.22/0.59    inference(subsumption_resolution,[],[f428,f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    k1_xboole_0 != sK1),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.59    inference(flattening,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.59    inference(negated_conjecture,[],[f18])).
% 0.22/0.59  fof(f18,conjecture,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).
% 0.22/0.59  fof(f428,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | ~spl12_7),
% 0.22/0.59    inference(subsumption_resolution,[],[f425,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    k1_xboole_0 != sK0),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f425,plain,(
% 0.22/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl12_7),
% 0.22/0.59    inference(resolution,[],[f379,f90])).
% 0.22/0.59  fof(f90,plain,(
% 0.22/0.59    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.59    inference(definition_unfolding,[],[f48,f65])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f379,plain,(
% 0.22/0.59    ( ! [X8,X9] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X8 | k1_xboole_0 = X9) ) | ~spl12_7),
% 0.22/0.59    inference(avatar_component_clause,[],[f378])).
% 0.22/0.59  fof(f378,plain,(
% 0.22/0.59    spl12_7 <=> ! [X9,X8] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X8 | k1_xboole_0 = X9)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.22/0.59  fof(f424,plain,(
% 0.22/0.59    ~spl12_11),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f423])).
% 0.22/0.59  fof(f423,plain,(
% 0.22/0.59    $false | ~spl12_11),
% 0.22/0.59    inference(subsumption_resolution,[],[f422,f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    k1_xboole_0 != sK2),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f422,plain,(
% 0.22/0.59    k1_xboole_0 = sK2 | ~spl12_11),
% 0.22/0.59    inference(subsumption_resolution,[],[f419,f51])).
% 0.22/0.59  fof(f419,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~spl12_11),
% 0.22/0.59    inference(resolution,[],[f391,f90])).
% 1.77/0.59  fof(f391,plain,(
% 1.77/0.59    ( ! [X0,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X3) ) | ~spl12_11),
% 1.77/0.59    inference(avatar_component_clause,[],[f390])).
% 1.77/0.59  fof(f390,plain,(
% 1.77/0.59    spl12_11 <=> ! [X3,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | k1_xboole_0 = X3)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.77/0.59  fof(f418,plain,(
% 1.77/0.59    ~spl12_10),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f417])).
% 1.77/0.59  fof(f417,plain,(
% 1.77/0.59    $false | ~spl12_10),
% 1.77/0.59    inference(subsumption_resolution,[],[f416,f52])).
% 1.77/0.59  fof(f416,plain,(
% 1.77/0.59    k1_xboole_0 = sK2 | ~spl12_10),
% 1.77/0.59    inference(subsumption_resolution,[],[f413,f50])).
% 1.77/0.59  fof(f413,plain,(
% 1.77/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl12_10),
% 1.77/0.59    inference(resolution,[],[f388,f90])).
% 1.77/0.59  fof(f388,plain,(
% 1.77/0.59    ( ! [X2,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | k1_xboole_0 = X2 | k1_xboole_0 = X1) ) | ~spl12_10),
% 1.77/0.59    inference(avatar_component_clause,[],[f387])).
% 1.77/0.59  fof(f387,plain,(
% 1.77/0.59    spl12_10 <=> ! [X1,X2] : (k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.77/0.59  fof(f410,plain,(
% 1.77/0.59    ~spl12_1 | ~spl12_9),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f404])).
% 1.77/0.59  fof(f404,plain,(
% 1.77/0.59    $false | (~spl12_1 | ~spl12_9)),
% 1.77/0.59    inference(resolution,[],[f400,f118])).
% 1.77/0.59  fof(f118,plain,(
% 1.77/0.59    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl12_1),
% 1.77/0.59    inference(avatar_component_clause,[],[f116])).
% 1.77/0.59  fof(f116,plain,(
% 1.77/0.59    spl12_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.77/0.59  fof(f400,plain,(
% 1.77/0.59    ( ! [X6,X4,X5] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))) ) | ~spl12_9),
% 1.77/0.59    inference(resolution,[],[f385,f66])).
% 1.77/0.59  fof(f66,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f27])).
% 1.77/0.59  fof(f27,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.77/0.59    inference(ennf_transformation,[],[f13])).
% 1.77/0.59  fof(f13,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.77/0.59  fof(f385,plain,(
% 1.77/0.59    ( ! [X4,X5] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))) ) | ~spl12_9),
% 1.77/0.59    inference(avatar_component_clause,[],[f384])).
% 1.77/0.59  fof(f384,plain,(
% 1.77/0.59    spl12_9 <=> ! [X5,X4] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.77/0.59  fof(f398,plain,(
% 1.77/0.59    ~spl12_1 | ~spl12_8),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f393])).
% 1.77/0.59  fof(f393,plain,(
% 1.77/0.59    $false | (~spl12_1 | ~spl12_8)),
% 1.77/0.59    inference(resolution,[],[f382,f118])).
% 1.77/0.59  fof(f382,plain,(
% 1.77/0.59    ( ! [X6,X7] : (~r2_hidden(sK4,k2_zfmisc_1(X6,X7))) ) | ~spl12_8),
% 1.77/0.59    inference(avatar_component_clause,[],[f381])).
% 1.77/0.59  fof(f381,plain,(
% 1.77/0.59    spl12_8 <=> ! [X7,X6] : ~r2_hidden(sK4,k2_zfmisc_1(X6,X7))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.77/0.59  fof(f392,plain,(
% 1.77/0.59    spl12_7 | spl12_8 | spl12_9 | spl12_10 | spl12_11),
% 1.77/0.59    inference(avatar_split_clause,[],[f376,f390,f387,f384,f381,f378])).
% 1.77/0.59  fof(f376,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) | ~r2_hidden(sK4,k2_zfmisc_1(X6,X7)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X9 | k1_xboole_0 = X8) )),
% 1.77/0.59    inference(subsumption_resolution,[],[f375,f350])).
% 1.77/0.59  fof(f350,plain,(
% 1.77/0.59    sK3 != k1_mcart_1(k1_mcart_1(sK4))),
% 1.77/0.59    inference(subsumption_resolution,[],[f349,f50])).
% 1.77/0.59  fof(f349,plain,(
% 1.77/0.59    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 1.77/0.59    inference(subsumption_resolution,[],[f348,f51])).
% 1.77/0.59  fof(f348,plain,(
% 1.77/0.59    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.77/0.59    inference(subsumption_resolution,[],[f347,f52])).
% 1.77/0.59  fof(f347,plain,(
% 1.77/0.59    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.77/0.59    inference(subsumption_resolution,[],[f342,f90])).
% 1.77/0.59  fof(f342,plain,(
% 1.77/0.59    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.77/0.59    inference(superposition,[],[f53,f93])).
% 1.77/0.59  fof(f93,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(definition_unfolding,[],[f76,f65])).
% 1.77/0.59  fof(f76,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f28])).
% 1.77/0.59  fof(f28,plain,(
% 1.77/0.59    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.77/0.59    inference(ennf_transformation,[],[f16])).
% 1.77/0.59  fof(f16,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.77/0.59  fof(f53,plain,(
% 1.77/0.59    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 1.77/0.59    inference(cnf_transformation,[],[f33])).
% 1.77/0.59  fof(f375,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | sK3 = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) | ~r2_hidden(sK4,k2_zfmisc_1(X6,X7)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X9 | k1_xboole_0 = X8) )),
% 1.77/0.59    inference(equality_resolution,[],[f365])).
% 1.77/0.59  fof(f365,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sK4 != X4 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | sK3 = k1_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2)) | ~r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X4,k2_zfmisc_1(X7,X8)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2)) | k1_xboole_0 = X10 | k1_xboole_0 = X9) )),
% 1.77/0.59    inference(subsumption_resolution,[],[f363,f52])).
% 1.77/0.59  fof(f363,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | sK3 = k1_mcart_1(k1_mcart_1(X4)) | sK4 != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2)) | ~r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X4,k2_zfmisc_1(X7,X8)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = X10 | k1_xboole_0 = X9) )),
% 1.77/0.59    inference(resolution,[],[f361,f304])).
% 1.77/0.59  fof(f304,plain,(
% 1.77/0.59    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(X7),X6) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.77/0.59    inference(duplicate_literal_removal,[],[f303])).
% 1.77/0.59  fof(f303,plain,(
% 1.77/0.59    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(X7),X6) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.77/0.59    inference(superposition,[],[f94,f91])).
% 1.77/0.59  fof(f91,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(definition_unfolding,[],[f78,f65])).
% 1.77/0.59  fof(f78,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f28])).
% 1.77/0.59  fof(f94,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.77/0.59    inference(definition_unfolding,[],[f80,f65])).
% 1.77/0.59  fof(f80,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f29])).
% 1.77/0.59  fof(f29,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.77/0.59    inference(ennf_transformation,[],[f12])).
% 1.77/0.59  fof(f12,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 1.77/0.59  fof(f361,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | sK4 != X0 | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X0,k2_zfmisc_1(X7,X8))) )),
% 1.77/0.59    inference(superposition,[],[f355,f179])).
% 1.77/0.59  fof(f179,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.77/0.59    inference(resolution,[],[f62,f61])).
% 1.77/0.59  fof(f61,plain,(
% 1.77/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f6])).
% 1.77/0.59  fof(f6,axiom,(
% 1.77/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.77/0.59  fof(f62,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f24])).
% 1.77/0.59  fof(f24,plain,(
% 1.77/0.59    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.77/0.59    inference(flattening,[],[f23])).
% 1.77/0.59  fof(f23,plain,(
% 1.77/0.59    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.77/0.59    inference(ennf_transformation,[],[f14])).
% 1.77/0.59  fof(f14,axiom,(
% 1.77/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.77/0.59  fof(f355,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sK4 != k4_tarski(k1_mcart_1(X0),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(X5,sK2) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7))) )),
% 1.77/0.59    inference(subsumption_resolution,[],[f352,f50])).
% 1.77/0.59  fof(f352,plain,(
% 1.77/0.59    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = sK0 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(X5,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X5) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7))) )),
% 1.77/0.59    inference(resolution,[],[f345,f337])).
% 1.77/0.59  fof(f337,plain,(
% 1.77/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X3) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5))) )),
% 1.77/0.59    inference(subsumption_resolution,[],[f335,f51])).
% 1.77/0.59  fof(f335,plain,(
% 1.77/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = sK1 | k1_xboole_0 = X1 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5))) )),
% 1.77/0.59    inference(resolution,[],[f332,f181])).
% 1.77/0.59  fof(f181,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | k1_mcart_1(X0) = sK3 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) )),
% 1.77/0.59    inference(superposition,[],[f89,f179])).
% 1.77/0.59  fof(f89,plain,(
% 1.77/0.59    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X5 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.77/0.59    inference(definition_unfolding,[],[f49,f64])).
% 1.77/0.59  fof(f64,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f7])).
% 1.77/0.59  fof(f7,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.77/0.59  fof(f49,plain,(
% 1.77/0.59    ( ! [X6,X7,X5] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f33])).
% 1.77/0.59  fof(f332,plain,(
% 1.77/0.59    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.77/0.59    inference(duplicate_literal_removal,[],[f331])).
% 1.77/0.59  fof(f331,plain,(
% 1.77/0.59    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.77/0.59    inference(superposition,[],[f95,f92])).
% 1.77/0.59  fof(f92,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(definition_unfolding,[],[f77,f65])).
% 1.77/0.59  fof(f77,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f28])).
% 1.77/0.59  fof(f95,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.77/0.59    inference(definition_unfolding,[],[f81,f65])).
% 1.77/0.59  fof(f81,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f30])).
% 1.77/0.59  fof(f30,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.77/0.59    inference(ennf_transformation,[],[f11])).
% 1.77/0.59  fof(f11,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 1.77/0.59  fof(f345,plain,(
% 1.77/0.59    ( ! [X6,X4,X7,X5] : (m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.77/0.59    inference(duplicate_literal_removal,[],[f344])).
% 1.77/0.59  fof(f344,plain,(
% 1.77/0.59    ( ! [X6,X4,X7,X5] : (m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.77/0.59    inference(superposition,[],[f96,f93])).
% 1.77/0.59  fof(f96,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.77/0.59    inference(definition_unfolding,[],[f82,f65])).
% 1.77/0.59  fof(f82,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f31])).
% 1.77/0.59  fof(f31,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.77/0.59    inference(ennf_transformation,[],[f10])).
% 1.77/0.59  fof(f10,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 1.77/0.59  fof(f240,plain,(
% 1.77/0.59    spl12_1 | spl12_2),
% 1.77/0.59    inference(avatar_split_clause,[],[f239,f120,f116])).
% 1.77/0.59  fof(f120,plain,(
% 1.77/0.59    spl12_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.77/0.59  fof(f239,plain,(
% 1.77/0.59    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.77/0.59    inference(resolution,[],[f90,f63])).
% 1.77/0.59  fof(f63,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f26])).
% 1.77/0.59  fof(f26,plain,(
% 1.77/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.77/0.59    inference(flattening,[],[f25])).
% 1.77/0.59  fof(f25,plain,(
% 1.77/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.77/0.59    inference(ennf_transformation,[],[f5])).
% 1.77/0.59  fof(f5,axiom,(
% 1.77/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.77/0.59  fof(f237,plain,(
% 1.77/0.59    ~spl12_6),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f236])).
% 1.77/0.59  fof(f236,plain,(
% 1.77/0.59    $false | ~spl12_6),
% 1.77/0.59    inference(subsumption_resolution,[],[f231,f51])).
% 1.77/0.59  fof(f231,plain,(
% 1.77/0.59    k1_xboole_0 = sK1 | ~spl12_6),
% 1.77/0.59    inference(resolution,[],[f212,f57])).
% 1.77/0.59  fof(f57,plain,(
% 1.77/0.59    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f39])).
% 1.77/0.59  fof(f39,plain,(
% 1.77/0.59    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.77/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f38])).
% 1.77/0.59  fof(f38,plain,(
% 1.77/0.59    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.77/0.59    introduced(choice_axiom,[])).
% 1.77/0.59  fof(f22,plain,(
% 1.77/0.59    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.77/0.59    inference(ennf_transformation,[],[f15])).
% 1.77/0.59  fof(f15,axiom,(
% 1.77/0.59    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.77/0.59  fof(f212,plain,(
% 1.77/0.59    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl12_6),
% 1.77/0.59    inference(avatar_component_clause,[],[f211])).
% 1.77/0.59  fof(f211,plain,(
% 1.77/0.59    spl12_6 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.77/0.59  fof(f229,plain,(
% 1.77/0.59    ~spl12_5),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f228])).
% 1.77/0.59  fof(f228,plain,(
% 1.77/0.59    $false | ~spl12_5),
% 1.77/0.59    inference(subsumption_resolution,[],[f223,f50])).
% 1.77/0.59  fof(f223,plain,(
% 1.77/0.59    k1_xboole_0 = sK0 | ~spl12_5),
% 1.77/0.59    inference(resolution,[],[f209,f57])).
% 1.77/0.59  fof(f209,plain,(
% 1.77/0.59    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl12_5),
% 1.77/0.59    inference(avatar_component_clause,[],[f208])).
% 1.77/0.59  fof(f208,plain,(
% 1.77/0.59    spl12_5 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 1.77/0.59  fof(f221,plain,(
% 1.77/0.59    ~spl12_4),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f220])).
% 1.77/0.59  fof(f220,plain,(
% 1.77/0.59    $false | ~spl12_4),
% 1.77/0.59    inference(subsumption_resolution,[],[f215,f52])).
% 1.77/0.59  fof(f215,plain,(
% 1.77/0.59    k1_xboole_0 = sK2 | ~spl12_4),
% 1.77/0.59    inference(resolution,[],[f198,f57])).
% 1.77/0.59  fof(f198,plain,(
% 1.77/0.59    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl12_4),
% 1.77/0.59    inference(avatar_component_clause,[],[f197])).
% 1.77/0.59  fof(f197,plain,(
% 1.77/0.59    spl12_4 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.77/0.59  fof(f213,plain,(
% 1.77/0.59    spl12_5 | spl12_6 | ~spl12_3),
% 1.77/0.59    inference(avatar_split_clause,[],[f200,f194,f211,f208])).
% 1.77/0.59  fof(f194,plain,(
% 1.77/0.59    spl12_3 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.77/0.59  fof(f200,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl12_3),
% 1.77/0.59    inference(resolution,[],[f195,f103])).
% 1.77/0.59  fof(f103,plain,(
% 1.77/0.59    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.77/0.59    inference(equality_resolution,[],[f102])).
% 1.77/0.59  fof(f102,plain,(
% 1.77/0.59    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.77/0.59    inference(equality_resolution,[],[f71])).
% 1.77/0.59  fof(f71,plain,(
% 1.77/0.59    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.77/0.59    inference(cnf_transformation,[],[f45])).
% 1.77/0.59  fof(f45,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.77/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f41,f44,f43,f42])).
% 1.77/0.59  fof(f42,plain,(
% 1.77/0.59    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.77/0.59    introduced(choice_axiom,[])).
% 1.77/0.59  fof(f43,plain,(
% 1.77/0.59    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 1.77/0.59    introduced(choice_axiom,[])).
% 1.77/0.59  fof(f44,plain,(
% 1.77/0.59    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)))),
% 1.77/0.59    introduced(choice_axiom,[])).
% 1.77/0.59  fof(f41,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.77/0.59    inference(rectify,[],[f40])).
% 1.77/0.59  fof(f40,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.77/0.59    inference(nnf_transformation,[],[f3])).
% 1.77/0.59  fof(f3,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.77/0.59  % (5244)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (5244)Memory used [KB]: 10874
% 1.77/0.59  % (5244)Time elapsed: 0.168 s
% 1.77/0.59  % (5244)------------------------------
% 1.77/0.59  % (5244)------------------------------
% 1.77/0.59  fof(f195,plain,(
% 1.77/0.59    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl12_3),
% 1.77/0.59    inference(avatar_component_clause,[],[f194])).
% 1.77/0.59  fof(f199,plain,(
% 1.77/0.59    spl12_3 | spl12_4 | ~spl12_2),
% 1.77/0.59    inference(avatar_split_clause,[],[f192,f120,f197,f194])).
% 1.77/0.59  fof(f192,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl12_2),
% 1.77/0.59    inference(subsumption_resolution,[],[f189,f137])).
% 1.77/0.59  fof(f137,plain,(
% 1.77/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.77/0.59    inference(backward_demodulation,[],[f130,f132])).
% 1.77/0.59  fof(f132,plain,(
% 1.77/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.77/0.59    inference(resolution,[],[f130,f57])).
% 1.77/0.59  fof(f130,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.77/0.59    inference(resolution,[],[f129,f54])).
% 1.77/0.59  fof(f54,plain,(
% 1.77/0.59    v1_xboole_0(k1_xboole_0)),
% 1.77/0.59    inference(cnf_transformation,[],[f2])).
% 1.77/0.59  fof(f2,axiom,(
% 1.77/0.59    v1_xboole_0(k1_xboole_0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.77/0.59  fof(f129,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.77/0.59    inference(resolution,[],[f66,f55])).
% 1.77/0.59  fof(f55,plain,(
% 1.77/0.59    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f37])).
% 1.77/0.59  fof(f37,plain,(
% 1.77/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.77/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.77/0.59  fof(f36,plain,(
% 1.77/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.77/0.59    introduced(choice_axiom,[])).
% 1.77/0.59  fof(f35,plain,(
% 1.77/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.77/0.59    inference(rectify,[],[f34])).
% 1.77/0.59  fof(f34,plain,(
% 1.77/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.77/0.59    inference(nnf_transformation,[],[f1])).
% 1.77/0.59  fof(f1,axiom,(
% 1.77/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.77/0.59  fof(f189,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK2) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl12_2),
% 1.77/0.59    inference(superposition,[],[f103,f124])).
% 1.77/0.59  fof(f124,plain,(
% 1.77/0.59    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl12_2),
% 1.77/0.59    inference(resolution,[],[f122,f112])).
% 1.77/0.59  fof(f112,plain,(
% 1.77/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.77/0.59    inference(resolution,[],[f57,f55])).
% 1.77/0.59  fof(f122,plain,(
% 1.77/0.59    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl12_2),
% 1.77/0.59    inference(avatar_component_clause,[],[f120])).
% 1.77/0.59  % SZS output end Proof for theBenchmark
% 1.77/0.59  % (5226)------------------------------
% 1.77/0.59  % (5226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (5226)Termination reason: Refutation
% 1.77/0.59  
% 1.77/0.59  % (5226)Memory used [KB]: 11129
% 1.77/0.59  % (5226)Time elapsed: 0.175 s
% 1.77/0.59  % (5226)------------------------------
% 1.77/0.59  % (5226)------------------------------
% 1.77/0.60  % (5218)Success in time 0.23 s
%------------------------------------------------------------------------------
