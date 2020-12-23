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
% DateTime   : Thu Dec  3 12:59:27 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 316 expanded)
%              Number of leaves         :   13 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          :  324 (2323 expanded)
%              Number of equality atoms :  186 (1370 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f116,f122,f128,f148])).

fof(f148,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f146,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).

fof(f13,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f146,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f145,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f145,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f144,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f144,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f143,f24])).

fof(f24,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f143,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(resolution,[],[f132,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f132,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
        | sK3 = k6_mcart_1(X3,X4,X5,sK4)
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4
        | k1_xboole_0 = X3 )
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f71,f93])).

fof(f93,plain,
    ( sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_4
  <=> sK3 = sK6(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f71,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | sK6(sK0,sK1,sK2,sK4) = k6_mcart_1(X3,X4,X5,sK4)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f50,f58])).

fof(f58,plain,(
    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f57,f21])).

fof(f57,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f56,f22])).

fof(f56,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f52,f23])).

fof(f52,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f25,f26])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f17,f16,f15])).

fof(f15,plain,(
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

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f25,f26])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X6
                & k6_mcart_1(X0,X1,X2,X3) = X5
                & k5_mcart_1(X0,X1,X2,X3) = X4 )
              | k3_mcart_1(X4,X5,X6) != X3 )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

fof(f128,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f126,f21])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f125,f22])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f124,f23])).

fof(f124,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(subsumption_resolution,[],[f123,f38])).

fof(f123,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_3
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f122,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f120,f21])).

fof(f120,plain,
    ( k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f119,f22])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f118,f23])).

fof(f118,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(subsumption_resolution,[],[f117,f38])).

fof(f117,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_2
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f116,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f114,f21])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f113,f22])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f112,f23])).

fof(f112,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(subsumption_resolution,[],[f111,f38])).

fof(f111,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_1
  <=> m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f94,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f77,f91,f87,f83,f79])).

fof(f77,plain,
    ( sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( sK4 != sK4
    | sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(superposition,[],[f37,f58])).

fof(f37,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f20,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f14])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 16:52:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.52  % (23405)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (23407)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.52  % (23416)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.53  % (23413)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (23408)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.53  % (23408)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.54  % (23424)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f149,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(avatar_sat_refutation,[],[f94,f116,f122,f128,f148])).
% 0.23/0.54  fof(f148,plain,(
% 0.23/0.54    ~spl8_4),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f147])).
% 0.23/0.54  fof(f147,plain,(
% 0.23/0.54    $false | ~spl8_4),
% 0.23/0.54    inference(subsumption_resolution,[],[f146,f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    k1_xboole_0 != sK0),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f13])).
% 0.23/0.54  fof(f13,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f9,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.23/0.54    inference(flattening,[],[f8])).
% 0.23/0.54  fof(f8,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.23/0.54    inference(negated_conjecture,[],[f6])).
% 0.23/0.54  fof(f6,conjecture,(
% 0.23/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.23/0.54  fof(f146,plain,(
% 0.23/0.54    k1_xboole_0 = sK0 | ~spl8_4),
% 0.23/0.54    inference(subsumption_resolution,[],[f145,f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    k1_xboole_0 != sK1),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f145,plain,(
% 0.23/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_4),
% 0.23/0.54    inference(subsumption_resolution,[],[f144,f23])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    k1_xboole_0 != sK2),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f144,plain,(
% 0.23/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_4),
% 0.23/0.54    inference(subsumption_resolution,[],[f143,f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f143,plain,(
% 0.23/0.54    sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_4),
% 0.23/0.54    inference(resolution,[],[f132,f38])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.23/0.54    inference(definition_unfolding,[],[f19,f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f132,plain,(
% 0.23/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | sK3 = k6_mcart_1(X3,X4,X5,sK4) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3) ) | ~spl8_4),
% 0.23/0.54    inference(backward_demodulation,[],[f71,f93])).
% 0.23/0.54  fof(f93,plain,(
% 0.23/0.54    sK3 = sK6(sK0,sK1,sK2,sK4) | ~spl8_4),
% 0.23/0.54    inference(avatar_component_clause,[],[f91])).
% 0.23/0.54  fof(f91,plain,(
% 0.23/0.54    spl8_4 <=> sK3 = sK6(sK0,sK1,sK2,sK4)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.23/0.54  fof(f71,plain,(
% 0.23/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | sK6(sK0,sK1,sK2,sK4) = k6_mcart_1(X3,X4,X5,sK4) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3) )),
% 0.23/0.54    inference(superposition,[],[f50,f58])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.23/0.54    inference(subsumption_resolution,[],[f57,f21])).
% 0.23/0.54  fof(f57,plain,(
% 0.23/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK0),
% 0.23/0.54    inference(subsumption_resolution,[],[f56,f22])).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.54    inference(subsumption_resolution,[],[f52,f23])).
% 0.23/0.54  fof(f52,plain,(
% 0.23/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.23/0.54    inference(resolution,[],[f38,f42])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(definition_unfolding,[],[f33,f25,f26])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f17,f16,f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f11,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.23/0.54    inference(ennf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.23/0.54  fof(f50,plain,(
% 0.23/0.54    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(equality_resolution,[],[f47])).
% 0.23/0.54  fof(f47,plain,(
% 0.23/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(definition_unfolding,[],[f35,f25,f26])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k3_mcart_1(X4,X5,X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f12,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.23/0.54    inference(ennf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : ~(? [X3] : (? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).
% 0.23/0.54  fof(f128,plain,(
% 0.23/0.54    spl8_3),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f127])).
% 0.23/0.54  fof(f127,plain,(
% 0.23/0.54    $false | spl8_3),
% 0.23/0.54    inference(subsumption_resolution,[],[f126,f21])).
% 0.23/0.54  fof(f126,plain,(
% 0.23/0.54    k1_xboole_0 = sK0 | spl8_3),
% 0.23/0.54    inference(subsumption_resolution,[],[f125,f22])).
% 0.23/0.54  fof(f125,plain,(
% 0.23/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.23/0.54    inference(subsumption_resolution,[],[f124,f23])).
% 0.23/0.54  fof(f124,plain,(
% 0.23/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.23/0.54    inference(subsumption_resolution,[],[f123,f38])).
% 0.23/0.54  fof(f123,plain,(
% 0.23/0.54    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.23/0.54    inference(resolution,[],[f89,f43])).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(definition_unfolding,[],[f32,f26])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f89,plain,(
% 0.23/0.54    ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | spl8_3),
% 0.23/0.54    inference(avatar_component_clause,[],[f87])).
% 0.23/0.54  fof(f87,plain,(
% 0.23/0.54    spl8_3 <=> m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.23/0.54  fof(f122,plain,(
% 0.23/0.54    spl8_2),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f121])).
% 0.23/0.54  fof(f121,plain,(
% 0.23/0.54    $false | spl8_2),
% 0.23/0.54    inference(subsumption_resolution,[],[f120,f21])).
% 0.23/0.54  fof(f120,plain,(
% 0.23/0.54    k1_xboole_0 = sK0 | spl8_2),
% 0.23/0.54    inference(subsumption_resolution,[],[f119,f22])).
% 0.23/0.54  fof(f119,plain,(
% 0.23/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.23/0.54    inference(subsumption_resolution,[],[f118,f23])).
% 0.23/0.54  fof(f118,plain,(
% 0.23/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.23/0.54    inference(subsumption_resolution,[],[f117,f38])).
% 0.23/0.54  fof(f117,plain,(
% 0.23/0.54    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.23/0.54    inference(resolution,[],[f85,f44])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(definition_unfolding,[],[f31,f26])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f85,plain,(
% 0.23/0.54    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | spl8_2),
% 0.23/0.54    inference(avatar_component_clause,[],[f83])).
% 0.23/0.54  fof(f83,plain,(
% 0.23/0.54    spl8_2 <=> m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.23/0.54  fof(f116,plain,(
% 0.23/0.54    spl8_1),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f115])).
% 0.23/0.54  fof(f115,plain,(
% 0.23/0.54    $false | spl8_1),
% 0.23/0.54    inference(subsumption_resolution,[],[f114,f21])).
% 0.23/0.54  fof(f114,plain,(
% 0.23/0.54    k1_xboole_0 = sK0 | spl8_1),
% 0.23/0.54    inference(subsumption_resolution,[],[f113,f22])).
% 0.23/0.54  fof(f113,plain,(
% 0.23/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.23/0.54    inference(subsumption_resolution,[],[f112,f23])).
% 0.23/0.54  fof(f112,plain,(
% 0.23/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.23/0.54    inference(subsumption_resolution,[],[f111,f38])).
% 0.23/0.54  fof(f111,plain,(
% 0.23/0.54    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.23/0.54    inference(resolution,[],[f81,f45])).
% 0.23/0.54  fof(f45,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(definition_unfolding,[],[f30,f26])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f81,plain,(
% 0.23/0.54    ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) | spl8_1),
% 0.23/0.54    inference(avatar_component_clause,[],[f79])).
% 0.23/0.54  fof(f79,plain,(
% 0.23/0.54    spl8_1 <=> m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.23/0.54  fof(f94,plain,(
% 0.23/0.54    ~spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4),
% 0.23/0.54    inference(avatar_split_clause,[],[f77,f91,f87,f83,f79])).
% 0.23/0.54  fof(f77,plain,(
% 0.23/0.54    sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.23/0.54    inference(trivial_inequality_removal,[],[f69])).
% 0.23/0.54  fof(f69,plain,(
% 0.23/0.54    sK4 != sK4 | sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.23/0.54    inference(superposition,[],[f37,f58])).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f20,f25])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (23408)------------------------------
% 0.23/0.54  % (23408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (23408)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (23408)Memory used [KB]: 10746
% 0.23/0.54  % (23408)Time elapsed: 0.111 s
% 0.23/0.54  % (23408)------------------------------
% 0.23/0.54  % (23408)------------------------------
% 0.23/0.54  % (23399)Success in time 0.168 s
%------------------------------------------------------------------------------
