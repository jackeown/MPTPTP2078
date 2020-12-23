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
% DateTime   : Thu Dec  3 12:59:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 319 expanded)
%              Number of leaves         :    8 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          :  287 (3221 expanded)
%              Number of equality atoms :  200 (2572 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f46,f59,f72])).

fof(f72,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f70,f10])).

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

fof(f70,plain,
    ( k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f69,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f68,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f67,f16])).

fof(f16,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k2_mcart_1(sK6) != k2_mcart_1(sK6)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(superposition,[],[f65,f22])).

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

fof(f65,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f64,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | k1_xboole_0 = sK3
    | spl8_3 ),
    inference(subsumption_resolution,[],[f63,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_3 ),
    inference(subsumption_resolution,[],[f62,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_3 ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f33,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(forward_demodulation,[],[f17,f18])).

fof(f18,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_3 ),
    inference(superposition,[],[f60,f22])).

fof(f60,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_3 ),
    inference(forward_demodulation,[],[f31,f18])).

fof(f31,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl8_3
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f59,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f57,f10])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f56,f11])).

fof(f56,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f55,f12])).

fof(f55,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f54,f16])).

fof(f54,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(trivial_inequality_removal,[],[f53])).

fof(f53,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) != k2_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(superposition,[],[f52,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f51,f13])).

fof(f51,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK3
    | spl8_2 ),
    inference(subsumption_resolution,[],[f50,f14])).

fof(f50,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_2 ),
    inference(subsumption_resolution,[],[f49,f15])).

fof(f49,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_2 ),
    inference(subsumption_resolution,[],[f48,f33])).

fof(f48,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_2 ),
    inference(superposition,[],[f47,f21])).

fof(f47,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_2 ),
    inference(forward_demodulation,[],[f28,f18])).

fof(f28,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl8_2
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f46,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f44,f10])).

fof(f44,plain,
    ( k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f43,f11])).

fof(f43,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f42,f12])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f41,f16])).

fof(f41,plain,
    ( ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) != k1_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(superposition,[],[f39,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f38,f13])).

fof(f38,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK3
    | spl8_1 ),
    inference(subsumption_resolution,[],[f37,f14])).

fof(f37,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_1 ),
    inference(subsumption_resolution,[],[f36,f15])).

fof(f36,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_1 ),
    inference(subsumption_resolution,[],[f35,f33])).

fof(f35,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | ~ m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl8_1 ),
    inference(superposition,[],[f34,f20])).

fof(f34,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6)
    | spl8_1 ),
    inference(forward_demodulation,[],[f25,f18])).

fof(f25,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl8_1
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:19:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (22075)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (22072)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (22076)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (22083)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (22072)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f32,f46,f59,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl8_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    $false | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f70,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    (((k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7) | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7)) & sK6 = sK7 & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f4,f8,f7,f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5] : (? [X6] : (? [X7] : ((k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7) | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7) | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7)) & X6 = X7 & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X6] : (? [X7] : ((k7_mcart_1(sK0,sK1,sK2,X6) != k7_mcart_1(sK3,sK4,sK5,X7) | k6_mcart_1(sK0,sK1,sK2,X6) != k6_mcart_1(sK3,sK4,sK5,X7) | k5_mcart_1(sK0,sK1,sK2,X6) != k5_mcart_1(sK3,sK4,sK5,X7)) & X6 = X7 & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5))) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X6] : (? [X7] : ((k7_mcart_1(sK0,sK1,sK2,X6) != k7_mcart_1(sK3,sK4,sK5,X7) | k6_mcart_1(sK0,sK1,sK2,X6) != k6_mcart_1(sK3,sK4,sK5,X7) | k5_mcart_1(sK0,sK1,sK2,X6) != k5_mcart_1(sK3,sK4,sK5,X7)) & X6 = X7 & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5))) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => (? [X7] : ((k7_mcart_1(sK3,sK4,sK5,X7) != k7_mcart_1(sK0,sK1,sK2,sK6) | k6_mcart_1(sK3,sK4,sK5,X7) != k6_mcart_1(sK0,sK1,sK2,sK6) | k5_mcart_1(sK3,sK4,sK5,X7) != k5_mcart_1(sK0,sK1,sK2,sK6)) & sK6 = X7 & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5))) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X7] : ((k7_mcart_1(sK3,sK4,sK5,X7) != k7_mcart_1(sK0,sK1,sK2,sK6) | k6_mcart_1(sK3,sK4,sK5,X7) != k6_mcart_1(sK0,sK1,sK2,sK6) | k5_mcart_1(sK3,sK4,sK5,X7) != k5_mcart_1(sK0,sK1,sK2,sK6)) & sK6 = X7 & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5))) => ((k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7) | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7)) & sK6 = sK7 & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f4,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5] : (? [X6] : (? [X7] : ((k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7) | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7) | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7)) & X6 = X7 & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3,X4,X5] : ~(? [X6] : (? [X7] : (~(k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7) & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7) & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7)) & X6 = X7 & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f2])).
% 0.21/0.47  fof(f2,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : ~(? [X6] : (? [X7] : (~(k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7) & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7) & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7)) & X6 = X7 & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_mcart_1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k1_xboole_0 != sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f67,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    k2_mcart_1(sK6) != k2_mcart_1(sK6) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.21/0.47    inference(superposition,[],[f65,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    k1_xboole_0 != sK3),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | k1_xboole_0 = sK3 | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f63,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    k1_xboole_0 != sK4),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k1_xboole_0 != sK5),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f61,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.47    inference(forward_demodulation,[],[f17,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    sK6 = sK7),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | ~m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_3),
% 0.21/0.47    inference(superposition,[],[f60,f22])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK6) | spl8_3),
% 0.21/0.47    inference(forward_demodulation,[],[f31,f18])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) | spl8_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl8_3 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK7)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl8_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    $false | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f10])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f11])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f12])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f54,f16])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    k2_mcart_1(k1_mcart_1(sK6)) != k2_mcart_1(k1_mcart_1(sK6)) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.21/0.47    inference(superposition,[],[f52,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f51,f13])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK3 | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f14])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f49,f15])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f48,f33])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | ~m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_2),
% 0.21/0.47    inference(superposition,[],[f47,f21])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6) | spl8_2),
% 0.21/0.47    inference(forward_demodulation,[],[f28,f18])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7) | spl8_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    spl8_2 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK7)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl8_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    $false | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f44,f10])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f43,f11])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f42,f12])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f41,f16])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    k1_mcart_1(k1_mcart_1(sK6)) != k1_mcart_1(k1_mcart_1(sK6)) | ~m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.21/0.47    inference(superposition,[],[f39,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f38,f13])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK3 | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f37,f14])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f36,f15])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f35,f33])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | ~m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | spl8_1),
% 0.21/0.47    inference(superposition,[],[f34,f20])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6) | spl8_1),
% 0.21/0.47    inference(forward_demodulation,[],[f25,f18])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) | spl8_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    spl8_1 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK7)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f30,f27,f24])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7) | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22072)------------------------------
% 0.21/0.47  % (22072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22072)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22072)Memory used [KB]: 10618
% 0.21/0.47  % (22072)Time elapsed: 0.067 s
% 0.21/0.47  % (22072)------------------------------
% 0.21/0.47  % (22072)------------------------------
% 0.21/0.47  % (22069)Success in time 0.11 s
%------------------------------------------------------------------------------
