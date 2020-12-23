%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 217 expanded)
%              Number of leaves         :   24 ( 117 expanded)
%              Depth                    :    6
%              Number of atoms          :  316 (1357 expanded)
%              Number of equality atoms :  172 ( 975 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f48,f52,f56,f60,f64,f68,f73,f78,f87,f94,f103,f108,f111,f120,f125,f128])).

fof(f128,plain,
    ( spl8_12
    | spl8_11
    | spl8_10
    | ~ spl8_6
    | spl8_21 ),
    inference(avatar_split_clause,[],[f127,f123,f42,f58,f62,f66])).

fof(f66,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f62,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f58,plain,
    ( spl8_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f42,plain,
    ( spl8_6
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f123,plain,
    ( spl8_21
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f127,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_21 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k2_mcart_1(sK6) != k2_mcart_1(sK6)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_21 ),
    inference(superposition,[],[f124,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f124,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl8_9
    | spl8_8
    | spl8_7
    | ~ spl8_14
    | ~ spl8_21
    | spl8_20 ),
    inference(avatar_split_clause,[],[f121,f118,f123,f76,f46,f50,f54])).

fof(f54,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f50,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f46,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f76,plain,
    ( spl8_14
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f118,plain,
    ( spl8_20
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f121,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_20 ),
    inference(superposition,[],[f119,f22])).

fof(f119,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( ~ spl8_20
    | spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f116,f34,f30,f118])).

fof(f30,plain,
    ( spl8_3
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f34,plain,
    ( spl8_4
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f116,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f31,f35])).

fof(f35,plain,
    ( sK6 = sK7
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f31,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f111,plain,
    ( spl8_12
    | spl8_11
    | spl8_10
    | ~ spl8_6
    | spl8_18 ),
    inference(avatar_split_clause,[],[f110,f106,f42,f58,f62,f66])).

fof(f106,plain,
    ( spl8_18
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f110,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_18 ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) != k2_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_18 ),
    inference(superposition,[],[f107,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f107,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl8_9
    | spl8_8
    | spl8_7
    | ~ spl8_14
    | ~ spl8_18
    | spl8_17 ),
    inference(avatar_split_clause,[],[f104,f101,f106,f76,f46,f50,f54])).

fof(f101,plain,
    ( spl8_17
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f104,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_17 ),
    inference(superposition,[],[f102,f21])).

fof(f102,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( ~ spl8_17
    | spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f99,f34,f27,f101])).

fof(f27,plain,
    ( spl8_2
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f99,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f28,f35])).

fof(f28,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f94,plain,
    ( spl8_12
    | spl8_11
    | spl8_10
    | ~ spl8_6
    | spl8_15 ),
    inference(avatar_split_clause,[],[f89,f85,f42,f58,f62,f66])).

fof(f85,plain,
    ( spl8_15
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f89,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_15 ),
    inference(trivial_inequality_removal,[],[f88])).

fof(f88,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) != k1_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_15 ),
    inference(superposition,[],[f86,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f86,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( spl8_9
    | spl8_8
    | spl8_7
    | ~ spl8_14
    | ~ spl8_15
    | spl8_13 ),
    inference(avatar_split_clause,[],[f79,f71,f85,f76,f46,f50,f54])).

fof(f71,plain,
    ( spl8_13
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f79,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_13 ),
    inference(superposition,[],[f72,f20])).

fof(f72,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( spl8_14
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f74,f38,f34,f76])).

fof(f38,plain,
    ( spl8_5
  <=> m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f74,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(superposition,[],[f39,f35])).

fof(f39,plain,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f73,plain,
    ( ~ spl8_13
    | spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f69,f34,f24,f71])).

fof(f24,plain,
    ( spl8_1
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f69,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_1
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f25,f35])).

fof(f25,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f68,plain,(
    ~ spl8_12 ),
    inference(avatar_split_clause,[],[f10,f66])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
      | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
      | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) )
    & sK6 = sK7
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f4,f8,f7,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                  | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                  | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(sK0,sK1,sK2,X6) != k7_mcart_1(sK3,sK4,sK5,X7)
                | k6_mcart_1(sK0,sK1,sK2,X6) != k6_mcart_1(sK3,sK4,sK5,X7)
                | k5_mcart_1(sK0,sK1,sK2,X6) != k5_mcart_1(sK3,sK4,sK5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( k7_mcart_1(sK0,sK1,sK2,X6) != k7_mcart_1(sK3,sK4,sK5,X7)
              | k6_mcart_1(sK0,sK1,sK2,X6) != k6_mcart_1(sK3,sK4,sK5,X7)
              | k5_mcart_1(sK0,sK1,sK2,X6) != k5_mcart_1(sK3,sK4,sK5,X7) )
            & X6 = X7
            & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ? [X7] :
          ( ( k7_mcart_1(sK3,sK4,sK5,X7) != k7_mcart_1(sK0,sK1,sK2,sK6)
            | k6_mcart_1(sK3,sK4,sK5,X7) != k6_mcart_1(sK0,sK1,sK2,sK6)
            | k5_mcart_1(sK3,sK4,sK5,X7) != k5_mcart_1(sK0,sK1,sK2,sK6) )
          & sK6 = X7
          & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X7] :
        ( ( k7_mcart_1(sK3,sK4,sK5,X7) != k7_mcart_1(sK0,sK1,sK2,sK6)
          | k6_mcart_1(sK3,sK4,sK5,X7) != k6_mcart_1(sK0,sK1,sK2,sK6)
          | k5_mcart_1(sK3,sK4,sK5,X7) != k5_mcart_1(sK0,sK1,sK2,sK6) )
        & sK6 = X7
        & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
   => ( ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
        | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
        | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) )
      & sK6 = sK7
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ~ ( ? [X6] :
              ( ? [X7] :
                  ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                      & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                      & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                  & X6 = X7
                  & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( ? [X6] :
            ( ? [X7] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                    & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                    & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_mcart_1)).

fof(f64,plain,(
    ~ spl8_11 ),
    inference(avatar_split_clause,[],[f11,f62])).

fof(f11,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ~ spl8_10 ),
    inference(avatar_split_clause,[],[f12,f58])).

fof(f12,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f13,f54])).

fof(f13,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f14,f50])).

fof(f14,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f15,f46])).

fof(f15,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f19,f30,f27,f24])).

fof(f19,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
