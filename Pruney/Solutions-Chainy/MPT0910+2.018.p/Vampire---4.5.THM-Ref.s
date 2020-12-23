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
% DateTime   : Thu Dec  3 12:59:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 143 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   24
%              Number of atoms          :  280 ( 941 expanded)
%              Number of equality atoms :  179 ( 575 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f120])).

fof(f120,plain,
    ( ~ spl8_4
    | spl8_3
    | spl8_2
    | spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f115,f62,f42,f47,f52,f57])).

fof(f57,plain,
    ( spl8_4
  <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f52,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f47,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f42,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f62,plain,
    ( spl8_5
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | spl8_5 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( sK3 != sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | sK4 != sK4
    | spl8_5 ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( sK3 != sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | sK4 != sK4
    | spl8_5 ),
    inference(superposition,[],[f64,f103])).

fof(f103,plain,(
    ! [X6,X8,X7,X5] :
      ( sK3 = k6_mcart_1(X6,X7,X8,X5)
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X8
      | ~ m1_subset_1(X5,k3_zfmisc_1(X6,X7,X8))
      | ~ m1_subset_1(X5,k3_zfmisc_1(sK0,sK1,sK2))
      | sK4 != X5 ) ),
    inference(superposition,[],[f39,f88])).

fof(f88,plain,(
    ! [X1] :
      ( k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X1),sK3),sK7(sK0,sK1,sK2,X1)) = X1
      | ~ m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2))
      | sK4 != X1 ) ),
    inference(global_subsumption,[],[f17,f18,f19,f87])).

fof(f87,plain,(
    ! [X1] :
      ( k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X1),sK3),sK7(sK0,sK1,sK2,X1)) = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK0
      | sK4 != X1 ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X1] :
      ( k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X1),sK3),sK7(sK0,sK1,sK2,X1)) = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK0
      | sK4 != X1
      | ~ m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    inference(superposition,[],[f34,f82])).

fof(f82,plain,(
    ! [X0] :
      ( sK3 = sK6(sK0,sK1,sK2,X0)
      | sK4 != X0
      | ~ m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    inference(global_subsumption,[],[f17,f18,f19,f81])).

fof(f81,plain,(
    ! [X0] :
      ( sK4 != X0
      | sK3 = sK6(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2 ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( sK4 != X0
      | sK3 = sK6(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f79,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(X1,sK1,sK2,X0),sK0)
      | sK4 != X0
      | sK3 = sK6(X1,sK1,sK2,X0)
      | ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2))
      | k1_xboole_0 = X1 ) ),
    inference(global_subsumption,[],[f18,f19,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( sK4 != X0
      | ~ m1_subset_1(sK5(X1,sK1,sK2,X0),sK0)
      | sK3 = sK6(X1,sK1,sK2,X0)
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2 ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sK4 != X0
      | ~ m1_subset_1(sK5(X1,sK1,sK2,X0),sK0)
      | sK3 = sK6(X1,sK1,sK2,X0)
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f76,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK2,X2),sK1)
      | sK4 != X2
      | ~ m1_subset_1(sK5(X0,X1,sK2,X2),sK0)
      | sK3 = sK6(X0,X1,sK2,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f19,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK2,X2),sK1)
      | sK4 != X2
      | ~ m1_subset_1(sK5(X0,X1,sK2,X2),sK0)
      | sK3 = sK6(X0,X1,sK2,X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,sK2,X2),sK1)
      | sK4 != X2
      | ~ m1_subset_1(sK5(X0,X1,sK2,X2),sK0)
      | sK3 = sK6(X0,X1,sK2,X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f68,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,X3),sK2)
      | ~ m1_subset_1(sK6(X0,X1,X2,X3),sK1)
      | sK4 != X3
      | ~ m1_subset_1(sK5(X0,X1,X2,X3),sK0)
      | sK3 = sK6(X0,X1,X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f33,f34])).

fof(f33,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X6 ) ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f15,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X6 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k6_mcart_1(X0,X1,X2,X3) = X5 ) ),
    inference(definition_unfolding,[],[f31,f21])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k3_mcart_1(X4,X5,X6) != X3
      | k6_mcart_1(X0,X1,X2,X3) = X5 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f64,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f20,f62])).

fof(f20,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f16,f57])).

fof(f16,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f50,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f45,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f17,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.51  % (29872)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (29863)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (29881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (29861)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (29880)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (29864)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (29870)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (29860)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (29881)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~spl8_4 | spl8_3 | spl8_2 | spl8_1 | spl8_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f115,f62,f42,f47,f52,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl8_4 <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl8_3 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl8_1 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl8_5 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | spl8_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    sK3 != sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | sK4 != sK4 | spl8_5),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    sK3 != sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | sK4 != sK4 | spl8_5),
% 0.21/0.52    inference(superposition,[],[f64,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X5] : (sK3 = k6_mcart_1(X6,X7,X8,X5) | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k1_xboole_0 = X8 | ~m1_subset_1(X5,k3_zfmisc_1(X6,X7,X8)) | ~m1_subset_1(X5,k3_zfmisc_1(sK0,sK1,sK2)) | sK4 != X5) )),
% 0.21/0.52    inference(superposition,[],[f39,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X1] : (k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X1),sK3),sK7(sK0,sK1,sK2,X1)) = X1 | ~m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2)) | sK4 != X1) )),
% 0.21/0.52    inference(global_subsumption,[],[f17,f18,f19,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X1] : (k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X1),sK3),sK7(sK0,sK1,sK2,X1)) = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | sK4 != X1) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X1] : (k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X1),sK3),sK7(sK0,sK1,sK2,X1)) = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | sK4 != X1 | ~m1_subset_1(X1,k3_zfmisc_1(sK0,sK1,sK2))) )),
% 0.21/0.52    inference(superposition,[],[f34,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0] : (sK3 = sK6(sK0,sK1,sK2,X0) | sK4 != X0 | ~m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2))) )),
% 0.21/0.52    inference(global_subsumption,[],[f17,f18,f19,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (sK4 != X0 | sK3 = sK6(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0] : (sK4 != X0 | sK3 = sK6(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(resolution,[],[f79,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK5(X1,sK1,sK2,X0),sK0) | sK4 != X0 | sK3 = sK6(X1,sK1,sK2,X0) | ~m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2)) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(global_subsumption,[],[f18,f19,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK4 != X0 | ~m1_subset_1(sK5(X1,sK1,sK2,X0),sK0) | sK3 = sK6(X1,sK1,sK2,X0) | k1_xboole_0 = sK1 | ~m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2)) | k1_xboole_0 = X1 | k1_xboole_0 = sK2) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK4 != X0 | ~m1_subset_1(sK5(X1,sK1,sK2,X0),sK0) | sK3 = sK6(X1,sK1,sK2,X0) | k1_xboole_0 = sK1 | ~m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2)) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(resolution,[],[f76,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X0,X1,sK2,X2),sK1) | sK4 != X2 | ~m1_subset_1(sK5(X0,X1,sK2,X2),sK0) | sK3 = sK6(X0,X1,sK2,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(global_subsumption,[],[f19,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X0,X1,sK2,X2),sK1) | sK4 != X2 | ~m1_subset_1(sK5(X0,X1,sK2,X2),sK0) | sK3 = sK6(X0,X1,sK2,X2) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X0,X1,sK2,X2),sK1) | sK4 != X2 | ~m1_subset_1(sK5(X0,X1,sK2,X2),sK0) | sK3 = sK6(X0,X1,sK2,X2) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(X2,k3_zfmisc_1(X0,X1,sK2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f68,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,X3),sK2) | ~m1_subset_1(sK6(X0,X1,X2,X3),sK1) | sK4 != X3 | ~m1_subset_1(sK5(X0,X1,X2,X3),sK0) | sK3 = sK6(X0,X1,X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(superposition,[],[f33,f34])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X6) )),
% 0.21/0.52    inference(definition_unfolding,[],[f15,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X6) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f21])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X1] : (k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k6_mcart_1(X0,X1,X2,X3) = X5) )),
% 0.21/0.52    inference(definition_unfolding,[],[f31,f21])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k3_mcart_1(X4,X5,X6) != X3 | k6_mcart_1(X0,X1,X2,X3) = X5) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) | spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f20,f62])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f16,f57])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f19,f52])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f18,f47])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ~spl8_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (29881)------------------------------
% 0.21/0.53  % (29881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29881)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (29881)Memory used [KB]: 10874
% 0.21/0.53  % (29881)Time elapsed: 0.069 s
% 0.21/0.53  % (29881)------------------------------
% 0.21/0.53  % (29881)------------------------------
% 0.21/0.53  % (29888)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (29851)Success in time 0.173 s
%------------------------------------------------------------------------------
