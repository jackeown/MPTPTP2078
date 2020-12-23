%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:27 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 317 expanded)
%              Number of leaves         :   13 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          :  332 (2331 expanded)
%              Number of equality atoms :  193 (1377 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f96,f102,f108,f128])).

fof(f128,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f126,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f125,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f124,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f124,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f123,f23])).

fof(f23,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(resolution,[],[f112,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f112,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
        | sK3 = k6_mcart_1(X3,X4,X5,sK4)
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4
        | k1_xboole_0 = X3 )
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f51,f73])).

fof(f73,plain,
    ( sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_4
  <=> sK3 = sK6(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f51,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | sK6(sK0,sK1,sK2,sK4) = k6_mcart_1(X3,X4,X5,sK4) ) ),
    inference(superposition,[],[f43,f48])).

fof(f48,plain,(
    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f47,f20])).

fof(f47,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f46,f21])).

fof(f46,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f45,f22])).

fof(f45,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f24,f25])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

% (6380)Refutation not found, incomplete strategy% (6380)------------------------------
% (6380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6380)Termination reason: Refutation not found, incomplete strategy

% (6380)Memory used [KB]: 1791
% (6380)Time elapsed: 0.126 s
% (6380)------------------------------
% (6380)------------------------------
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK7(X0,X1,X2,X3),X2)
            & m1_subset_1(sK6(X0,X1,X2,X3),X1)
            & m1_subset_1(sK5(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f9,f16,f15,f14])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK6(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f31,f24,f25])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

% (6390)Refutation not found, incomplete strategy% (6390)------------------------------
% (6390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6390)Termination reason: Refutation not found, incomplete strategy

% (6390)Memory used [KB]: 10746
% (6390)Time elapsed: 0.120 s
% (6390)------------------------------
% (6390)------------------------------
fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f108,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f106,f20])).

fof(f106,plain,
    ( k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f105,f21])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f104,f22])).

fof(f104,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f103,f34])).

fof(f103,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(resolution,[],[f69,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_3
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f102,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f100,f20])).

fof(f100,plain,
    ( k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f99,f21])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f98,f22])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_2
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f96,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f94,f20])).

fof(f94,plain,
    ( k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f92,f22])).

fof(f92,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f91,f34])).

fof(f91,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(resolution,[],[f61,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl8_1
  <=> m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f74,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f57,f71,f67,f63,f59])).

% (6403)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f57,plain,
    ( sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( sK4 != sK4
    | sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(superposition,[],[f33,f48])).

fof(f33,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f19,f24])).

% (6383)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f19,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:32:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.25/0.52  % (6389)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (6388)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.52  % (6381)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.52  % (6387)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.53  % (6407)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (6380)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (6390)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.53  % (6388)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f129,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f74,f96,f102,f108,f128])).
% 1.25/0.53  fof(f128,plain,(
% 1.25/0.53    ~spl8_4),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f127])).
% 1.25/0.53  fof(f127,plain,(
% 1.25/0.53    $false | ~spl8_4),
% 1.25/0.53    inference(subsumption_resolution,[],[f126,f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    k1_xboole_0 != sK0),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,plain,(
% 1.25/0.53    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f12])).
% 1.25/0.53  fof(f12,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f8,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.53    inference(flattening,[],[f7])).
% 1.25/0.53  fof(f7,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.53    inference(ennf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.25/0.53    inference(negated_conjecture,[],[f5])).
% 1.25/0.53  fof(f5,conjecture,(
% 1.25/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).
% 1.25/0.53  fof(f126,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | ~spl8_4),
% 1.25/0.53    inference(subsumption_resolution,[],[f125,f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    k1_xboole_0 != sK1),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f125,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_4),
% 1.25/0.53    inference(subsumption_resolution,[],[f124,f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    k1_xboole_0 != sK2),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f124,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_4),
% 1.25/0.53    inference(subsumption_resolution,[],[f123,f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f123,plain,(
% 1.25/0.53    sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_4),
% 1.25/0.53    inference(resolution,[],[f112,f34])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.25/0.53    inference(definition_unfolding,[],[f18,f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f112,plain,(
% 1.25/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | sK3 = k6_mcart_1(X3,X4,X5,sK4) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3) ) | ~spl8_4),
% 1.25/0.53    inference(backward_demodulation,[],[f51,f73])).
% 1.25/0.53  fof(f73,plain,(
% 1.25/0.53    sK3 = sK6(sK0,sK1,sK2,sK4) | ~spl8_4),
% 1.25/0.53    inference(avatar_component_clause,[],[f71])).
% 1.25/0.53  fof(f71,plain,(
% 1.25/0.53    spl8_4 <=> sK3 = sK6(sK0,sK1,sK2,sK4)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3 | sK6(sK0,sK1,sK2,sK4) = k6_mcart_1(X3,X4,X5,sK4)) )),
% 1.25/0.53    inference(superposition,[],[f43,f48])).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 1.25/0.53    inference(subsumption_resolution,[],[f47,f20])).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK0),
% 1.25/0.53    inference(subsumption_resolution,[],[f46,f21])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.25/0.53    inference(subsumption_resolution,[],[f45,f22])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.25/0.53    inference(resolution,[],[f34,f35])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(definition_unfolding,[],[f29,f24,f25])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  % (6380)Refutation not found, incomplete strategy% (6380)------------------------------
% 1.25/0.53  % (6380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (6380)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (6380)Memory used [KB]: 1791
% 1.25/0.53  % (6380)Time elapsed: 0.126 s
% 1.25/0.53  % (6380)------------------------------
% 1.25/0.53  % (6380)------------------------------
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f9,f16,f15,f14])).
% 1.25/0.53  fof(f14,plain,(
% 1.25/0.53    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f9,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.25/0.53    inference(ennf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5) )),
% 1.25/0.53    inference(equality_resolution,[],[f40])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f31,f24,f25])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f11])).
% 1.25/0.53  % (6390)Refutation not found, incomplete strategy% (6390)------------------------------
% 1.25/0.53  % (6390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (6390)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (6390)Memory used [KB]: 10746
% 1.25/0.53  % (6390)Time elapsed: 0.120 s
% 1.25/0.53  % (6390)------------------------------
% 1.25/0.53  % (6390)------------------------------
% 1.25/0.53  fof(f11,plain,(
% 1.25/0.53    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.53    inference(flattening,[],[f10])).
% 1.25/0.53  fof(f10,plain,(
% 1.25/0.53    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).
% 1.25/0.53  fof(f108,plain,(
% 1.25/0.53    spl8_3),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f107])).
% 1.25/0.53  fof(f107,plain,(
% 1.25/0.53    $false | spl8_3),
% 1.25/0.53    inference(subsumption_resolution,[],[f106,f20])).
% 1.25/0.53  fof(f106,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | spl8_3),
% 1.25/0.53    inference(subsumption_resolution,[],[f105,f21])).
% 1.25/0.53  fof(f105,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 1.25/0.53    inference(subsumption_resolution,[],[f104,f22])).
% 1.25/0.53  fof(f104,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 1.25/0.53    inference(subsumption_resolution,[],[f103,f34])).
% 1.25/0.53  fof(f103,plain,(
% 1.25/0.53    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 1.25/0.53    inference(resolution,[],[f69,f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(definition_unfolding,[],[f28,f25])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f69,plain,(
% 1.25/0.53    ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | spl8_3),
% 1.25/0.53    inference(avatar_component_clause,[],[f67])).
% 1.25/0.53  fof(f67,plain,(
% 1.25/0.53    spl8_3 <=> m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.25/0.53  fof(f102,plain,(
% 1.25/0.53    spl8_2),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f101])).
% 1.25/0.53  fof(f101,plain,(
% 1.25/0.53    $false | spl8_2),
% 1.25/0.53    inference(subsumption_resolution,[],[f100,f20])).
% 1.25/0.53  fof(f100,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | spl8_2),
% 1.25/0.53    inference(subsumption_resolution,[],[f99,f21])).
% 1.25/0.53  fof(f99,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 1.25/0.53    inference(subsumption_resolution,[],[f98,f22])).
% 1.25/0.53  fof(f98,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 1.25/0.53    inference(subsumption_resolution,[],[f97,f34])).
% 1.25/0.53  fof(f97,plain,(
% 1.25/0.53    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 1.25/0.53    inference(resolution,[],[f65,f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(definition_unfolding,[],[f27,f25])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f65,plain,(
% 1.25/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | spl8_2),
% 1.25/0.53    inference(avatar_component_clause,[],[f63])).
% 1.25/0.53  fof(f63,plain,(
% 1.25/0.53    spl8_2 <=> m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.25/0.53  fof(f96,plain,(
% 1.25/0.53    spl8_1),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f95])).
% 1.25/0.53  fof(f95,plain,(
% 1.25/0.53    $false | spl8_1),
% 1.25/0.53    inference(subsumption_resolution,[],[f94,f20])).
% 1.25/0.53  fof(f94,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | spl8_1),
% 1.25/0.53    inference(subsumption_resolution,[],[f93,f21])).
% 1.25/0.53  fof(f93,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 1.25/0.53    inference(subsumption_resolution,[],[f92,f22])).
% 1.25/0.53  fof(f92,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 1.25/0.53    inference(subsumption_resolution,[],[f91,f34])).
% 1.25/0.53  fof(f91,plain,(
% 1.25/0.53    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 1.25/0.53    inference(resolution,[],[f61,f38])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(definition_unfolding,[],[f26,f25])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) | spl8_1),
% 1.25/0.53    inference(avatar_component_clause,[],[f59])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    spl8_1 <=> m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.25/0.53  fof(f74,plain,(
% 1.25/0.53    ~spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4),
% 1.25/0.53    inference(avatar_split_clause,[],[f57,f71,f67,f63,f59])).
% 1.25/0.53  % (6403)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 1.25/0.53    inference(trivial_inequality_removal,[],[f49])).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    sK4 != sK4 | sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 1.25/0.53    inference(superposition,[],[f33,f48])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f19,f24])).
% 1.25/0.53  % (6383)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f13])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (6388)------------------------------
% 1.33/0.53  % (6388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (6388)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (6388)Memory used [KB]: 10746
% 1.33/0.53  % (6388)Time elapsed: 0.115 s
% 1.33/0.53  % (6388)------------------------------
% 1.33/0.53  % (6388)------------------------------
% 1.33/0.53  % (6379)Success in time 0.174 s
%------------------------------------------------------------------------------
