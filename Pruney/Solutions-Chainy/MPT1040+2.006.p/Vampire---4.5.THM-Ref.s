%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 249 expanded)
%              Number of leaves         :   35 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :  535 (1212 expanded)
%              Number of equality atoms :   90 ( 246 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f107,f113,f118,f127,f132,f143,f155,f161,f165,f173,f186,f190,f206,f211,f227,f279,f312])).

fof(f312,plain,
    ( ~ spl8_18
    | spl8_30 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl8_18
    | spl8_30 ),
    inference(subsumption_resolution,[],[f309,f278])).

fof(f278,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl8_30 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl8_30
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f309,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_18 ),
    inference(superposition,[],[f39,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_18
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f39,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f279,plain,
    ( ~ spl8_30
    | spl8_20
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f248,f224,f208,f276])).

fof(f208,plain,
    ( spl8_20
  <=> v1_partfun1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f224,plain,
    ( spl8_23
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f248,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl8_20
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f210,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_23 ),
    inference(resolution,[],[f226,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f226,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f224])).

fof(f210,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f227,plain,
    ( spl8_23
    | ~ spl8_16
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f222,f203,f163,f224])).

fof(f163,plain,
    ( spl8_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f203,plain,
    ( spl8_19
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f222,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_16
    | ~ spl8_19 ),
    inference(resolution,[],[f205,f164])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f205,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f211,plain,
    ( ~ spl8_20
    | ~ spl8_11
    | spl8_15 ),
    inference(avatar_split_clause,[],[f201,f152,f124,f208])).

fof(f124,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f152,plain,
    ( spl8_15
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f201,plain,
    ( ~ v1_partfun1(sK3,k1_xboole_0)
    | ~ spl8_11
    | spl8_15 ),
    inference(forward_demodulation,[],[f153,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f153,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f206,plain,
    ( spl8_19
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f198,f120,f115,f203])).

fof(f115,plain,
    ( spl8_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f120,plain,
    ( spl8_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f198,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f195,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f195,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f117,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f190,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_9
    | spl8_12
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_9
    | spl8_12
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f79,f74,f154,f89,f131,f112,f117,f65])).

fof(f65,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(X8,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK4(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK5(X0,X1,X2,X3))
                  & v1_partfun1(sK5(X0,X1,X2,X3),X0)
                  & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
                  & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK5(X0,X1,X2,X3)) )
                | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK6(X0,X1,X2,X7))
                    & v1_partfun1(sK6(X0,X1,X2,X7),X0)
                    & sK6(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK6(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X2,X5)
                | ~ v1_partfun1(X5,X0)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X2,X6)
                & v1_partfun1(X6,X0)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X2,X5)
              | ~ v1_partfun1(X5,X0)
              | sK4(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK4(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & sK4(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK5(X0,X1,X2,X3))
        & v1_partfun1(sK5(X0,X1,X2,X3),X0)
        & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK5(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK6(X0,X1,X2,X7))
        & v1_partfun1(sK6(X0,X1,X2,X7),X0)
        & sK6(X0,X1,X2,X7) = X7
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X6] :
                      ( r1_partfun1(X2,X6)
                      & v1_partfun1(X6,X0)
                      & X4 = X6
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X6) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ? [X9] :
                      ( r1_partfun1(X2,X9)
                      & v1_partfun1(X9,X0)
                      & X7 = X9
                      & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X9) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X3)
                  | ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) ) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f131,plain,
    ( ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_12
  <=> r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f89,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f154,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f74,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f79,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f186,plain,
    ( spl8_18
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f177,f170,f183])).

fof(f170,plain,
    ( spl8_17
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f177,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl8_17 ),
    inference(resolution,[],[f172,f41])).

fof(f172,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f173,plain,
    ( spl8_17
    | ~ spl8_13
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f166,f163,f137,f170])).

fof(f137,plain,
    ( spl8_13
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f166,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl8_13
    | ~ spl8_16 ),
    inference(resolution,[],[f164,f139])).

fof(f139,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f165,plain,
    ( spl8_16
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f135,f104,f163])).

fof(f104,plain,
    ( spl8_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f42,f106])).

fof(f106,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f161,plain,
    ( spl8_10
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl8_10
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f158,f122])).

fof(f122,plain,
    ( k1_xboole_0 != sK1
    | spl8_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f158,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_14 ),
    inference(resolution,[],[f150,f41])).

fof(f150,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_14
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f155,plain,
    ( spl8_14
    | spl8_15
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f146,f115,f92,f77,f152,f148])).

fof(f92,plain,
    ( spl8_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f146,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1)
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f145,f117])).

fof(f145,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f144,f79])).

fof(f144,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ spl8_5 ),
    inference(resolution,[],[f44,f94])).

fof(f94,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f143,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f134,f137])).

fof(f134,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f40,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f132,plain,(
    ~ spl8_12 ),
    inference(avatar_split_clause,[],[f38,f129])).

fof(f38,plain,(
    ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,k5_partfun1(sK0,sK1,sK2))
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(f127,plain,
    ( ~ spl8_10
    | spl8_11 ),
    inference(avatar_split_clause,[],[f37,f124,f120])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f35,f115])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f113,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f32,f110])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f107,plain,
    ( spl8_7
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f97,f82,f104])).

fof(f82,plain,
    ( spl8_3
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f97,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f84,f96])).

fof(f96,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_3 ),
    inference(resolution,[],[f41,f84])).

fof(f84,plain,
    ( v1_xboole_0(sK7)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f95,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f34,f92])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f60,f82])).

fof(f60,plain,(
    v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    v1_xboole_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f2,f29])).

fof(f29,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK7) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f80,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:50:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16799)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (16801)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (16801)Refutation not found, incomplete strategy% (16801)------------------------------
% 0.21/0.48  % (16801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16796)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (16801)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (16801)Memory used [KB]: 6396
% 0.21/0.49  % (16801)Time elapsed: 0.063 s
% 0.21/0.49  % (16801)------------------------------
% 0.21/0.49  % (16801)------------------------------
% 0.21/0.49  % (16788)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (16788)Refutation not found, incomplete strategy% (16788)------------------------------
% 0.21/0.50  % (16788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16788)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16788)Memory used [KB]: 10746
% 0.21/0.50  % (16788)Time elapsed: 0.074 s
% 0.21/0.50  % (16788)------------------------------
% 0.21/0.50  % (16788)------------------------------
% 0.21/0.50  % (16807)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (16806)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (16790)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (16790)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f107,f113,f118,f127,f132,f143,f155,f161,f165,f173,f186,f190,f206,f211,f227,f279,f312])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    ~spl8_18 | spl8_30),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f311])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    $false | (~spl8_18 | spl8_30)),
% 0.21/0.51    inference(subsumption_resolution,[],[f309,f278])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl8_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f276])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    spl8_30 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl8_18),
% 0.21/0.51    inference(superposition,[],[f39,f185])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl8_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl8_18 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    ~spl8_30 | spl8_20 | ~spl8_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f248,f224,f208,f276])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl8_20 <=> v1_partfun1(sK3,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    spl8_23 <=> v1_xboole_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (spl8_20 | ~spl8_23)),
% 0.21/0.51    inference(backward_demodulation,[],[f210,f230])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | ~spl8_23),
% 0.21/0.51    inference(resolution,[],[f226,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    v1_xboole_0(sK3) | ~spl8_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f224])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~v1_partfun1(sK3,k1_xboole_0) | spl8_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f208])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    spl8_23 | ~spl8_16 | ~spl8_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f222,f203,f163,f224])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl8_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl8_19 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    v1_xboole_0(sK3) | (~spl8_16 | ~spl8_19)),
% 0.21/0.51    inference(resolution,[],[f205,f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl8_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f163])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f203])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~spl8_20 | ~spl8_11 | spl8_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f201,f152,f124,f208])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl8_11 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl8_15 <=> v1_partfun1(sK3,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ~v1_partfun1(sK3,k1_xboole_0) | (~spl8_11 | spl8_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f153,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl8_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f124])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~v1_partfun1(sK3,sK0) | spl8_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f152])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl8_19 | ~spl8_9 | ~spl8_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f198,f120,f115,f203])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl8_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl8_10 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_9 | ~spl8_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f195,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_9 | ~spl8_10)),
% 0.21/0.51    inference(backward_demodulation,[],[f117,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl8_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_8 | ~spl8_9 | spl8_12 | ~spl8_15),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_8 | ~spl8_9 | spl8_12 | ~spl8_15)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f79,f74,f154,f89,f131,f112,f117,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X8,X1] : (~v1_funct_1(X2) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(X8,k5_partfun1(X0,X1,X2))) )),
% 0.21/0.51    inference(equality_resolution,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | sK4(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & ((r1_partfun1(X2,sK5(X0,X1,X2,X3)) & v1_partfun1(sK5(X0,X1,X2,X3),X0) & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK5(X0,X1,X2,X3))) | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8))) & ((r1_partfun1(X2,sK6(X0,X1,X2,X7)) & v1_partfun1(sK6(X0,X1,X2,X7),X0) & sK6(X0,X1,X2,X7) = X7 & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK6(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | sK4(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & sK4(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & sK4(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) => (r1_partfun1(X2,sK5(X0,X1,X2,X3)) & v1_partfun1(sK5(X0,X1,X2,X3),X0) & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK5(X0,X1,X2,X3))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X2,X9) & v1_partfun1(X9,X0) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X9)) => (r1_partfun1(X2,sK6(X0,X1,X2,X7)) & v1_partfun1(sK6(X0,X1,X2,X7),X0) & sK6(X0,X1,X2,X7) = X7 & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK6(X0,X1,X2,X7))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X2,X9) & v1_partfun1(X9,X0) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(rectify,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl8_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) | spl8_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl8_12 <=> r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    r1_partfun1(sK2,sK3) | ~spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl8_4 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    v1_partfun1(sK3,sK0) | ~spl8_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f152])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    v1_funct_1(sK2) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl8_1 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl8_2 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    spl8_18 | ~spl8_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f170,f183])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    spl8_17 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl8_17),
% 0.21/0.51    inference(resolution,[],[f172,f41])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl8_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f170])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl8_17 | ~spl8_13 | ~spl8_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f166,f163,f137,f170])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl8_13 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    v1_xboole_0(k6_partfun1(k1_xboole_0)) | (~spl8_13 | ~spl8_16)),
% 0.21/0.51    inference(resolution,[],[f164,f139])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl8_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f137])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl8_16 | ~spl8_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f135,f104,f163])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl8_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl8_7),
% 0.21/0.51    inference(resolution,[],[f42,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | ~spl8_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl8_10 | ~spl8_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    $false | (spl8_10 | ~spl8_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl8_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl8_14),
% 0.21/0.51    inference(resolution,[],[f150,f41])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~spl8_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl8_14 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl8_14 | spl8_15 | ~spl8_2 | ~spl8_5 | ~spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f146,f115,f92,f77,f152,f148])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl8_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1) | (~spl8_2 | ~spl8_5 | ~spl8_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f145,f117])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (~spl8_2 | ~spl8_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f79])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | ~spl8_5),
% 0.21/0.51    inference(resolution,[],[f44,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1) | ~spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl8_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f134,f137])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(superposition,[],[f40,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ~spl8_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f129])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    (~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f19,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X3] : (~r2_hidden(X3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~spl8_10 | spl8_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f124,f120])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f115])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl8_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f110])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl8_7 | ~spl8_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f82,f104])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl8_3 <=> v1_xboole_0(sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | ~spl8_3),
% 0.21/0.51    inference(backward_demodulation,[],[f84,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    k1_xboole_0 = sK7 | ~spl8_3),
% 0.21/0.51    inference(resolution,[],[f41,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    v1_xboole_0(sK7) | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl8_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f92])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl8_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f87])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    r1_partfun1(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl8_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f82])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v1_xboole_0(sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_xboole_0(sK7)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f2,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK7)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl8_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f72])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (16790)------------------------------
% 0.21/0.51  % (16790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16790)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (16790)Memory used [KB]: 6396
% 0.21/0.51  % (16790)Time elapsed: 0.101 s
% 0.21/0.51  % (16790)------------------------------
% 0.21/0.51  % (16790)------------------------------
% 0.21/0.51  % (16784)Success in time 0.151 s
%------------------------------------------------------------------------------
