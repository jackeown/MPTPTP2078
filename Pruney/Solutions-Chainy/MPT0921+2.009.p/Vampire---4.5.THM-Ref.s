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
% DateTime   : Thu Dec  3 12:59:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 435 expanded)
%              Number of leaves         :   12 ( 130 expanded)
%              Depth                    :   22
%              Number of atoms          :  499 (4143 expanded)
%              Number of equality atoms :  334 (2464 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22024)Refutation not found, incomplete strategy% (22024)------------------------------
% (22024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22024)Termination reason: Refutation not found, incomplete strategy

% (22024)Memory used [KB]: 10618
% (22024)Time elapsed: 0.136 s
% (22024)------------------------------
% (22024)------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f178,f187])).

fof(f187,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f185,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X8
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f185,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f184,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f184,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f183,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f183,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f182,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f182,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f181,f28])).

fof(f28,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f181,plain,
    ( sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl10_3 ),
    inference(resolution,[],[f125,f46])).

fof(f46,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f22,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,
    ( ! [X14,X12,X13,X11] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14))
        | sK4 = k10_mcart_1(X11,X12,X13,X14,sK5)
        | k1_xboole_0 = X11
        | k1_xboole_0 = X12
        | k1_xboole_0 = X13
        | k1_xboole_0 = X14 )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_3
  <=> ! [X11,X13,X12,X14] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14))
        | sK4 = k10_mcart_1(X11,X12,X13,X14,sK5)
        | k1_xboole_0 = X11
        | k1_xboole_0 = X12
        | k1_xboole_0 = X13
        | k1_xboole_0 = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f178,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f147,f112])).

fof(f112,plain,
    ( ! [X1] : k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_1
  <=> ! [X1] : k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f147,plain,
    ( sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_1 ),
    inference(superposition,[],[f28,f112])).

fof(f126,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f120,f124,f111])).

fof(f120,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14))
      | k1_xboole_0 = X14
      | k1_xboole_0 = X13
      | k1_xboole_0 = X12
      | k1_xboole_0 = X11
      | sK4 = k10_mcart_1(X11,X12,X13,X14,sK5)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X10 ) ),
    inference(superposition,[],[f62,f109])).

fof(f109,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(superposition,[],[f95,f105])).

fof(f105,plain,(
    ! [X20] :
      ( sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(subsumption_resolution,[],[f104,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f24])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f88,f25])).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f27])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f39,f30])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ( sK7(X0,X1,X2,X3,X4,X5) != X4
        & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
        & m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
        & m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
        & m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f14,f20,f19,f18,f17])).

fof(f17,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
     => ( ? [X7] :
            ( ? [X8] :
                ( ? [X9] :
                    ( X4 != X7
                    & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5
                    & m1_subset_1(X9,X3) )
                & m1_subset_1(X8,X2) )
            & m1_subset_1(X7,X1) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( ? [X9] :
                  ( X4 != X7
                  & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5
                  & m1_subset_1(X9,X3) )
              & m1_subset_1(X8,X2) )
          & m1_subset_1(X7,X1) )
     => ( ? [X8] :
            ( ? [X9] :
                ( sK7(X0,X1,X2,X3,X4,X5) != X4
                & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),X8,X9) = X5
                & m1_subset_1(X9,X3) )
            & m1_subset_1(X8,X2) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ? [X9] :
              ( sK7(X0,X1,X2,X3,X4,X5) != X4
              & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),X8,X9) = X5
              & m1_subset_1(X9,X3) )
          & m1_subset_1(X8,X2) )
     => ( ? [X9] :
            ( sK7(X0,X1,X2,X3,X4,X5) != X4
            & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),X9) = X5
            & m1_subset_1(X9,X3) )
        & m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( sK7(X0,X1,X2,X3,X4,X5) != X4
          & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),X9) = X5
          & m1_subset_1(X9,X3) )
     => ( sK7(X0,X1,X2,X3,X4,X5) != X4
        & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
        & m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f104,plain,(
    ! [X20] :
      ( sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(subsumption_resolution,[],[f103,f85])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f84,f24])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f83,f25])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f81,f27])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f40,f30])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X20] :
      ( sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(subsumption_resolution,[],[f102,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f78,f25])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f77,f26])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f76,f27])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f41,f30])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,(
    ! [X20] :
      ( sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(subsumption_resolution,[],[f101,f75])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f74,f24])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f72,f26])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f71,f27])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f42,f30])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X20] :
      ( sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,(
    ! [X20] :
      ( sK5 != sK5
      | sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(superposition,[],[f45,f95])).

fof(f45,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9)
      | sK4 = X8
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f23,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X8
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f24])).

fof(f94,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f93,f25])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f92,f26])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f91,f27])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f56,f46])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f43,f29,f30])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X7 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f37,f29,f30])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

% (22031)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (22025)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (22018)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (22025)Refutation not found, incomplete strategy% (22025)------------------------------
% 0.21/0.52  % (22025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22025)Memory used [KB]: 10618
% 0.21/0.52  % (22025)Time elapsed: 0.101 s
% 0.21/0.52  % (22025)------------------------------
% 0.21/0.52  % (22025)------------------------------
% 0.21/0.52  % (22032)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (22032)Refutation not found, incomplete strategy% (22032)------------------------------
% 0.21/0.52  % (22032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22041)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (22017)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (22032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22032)Memory used [KB]: 10618
% 0.21/0.52  % (22032)Time elapsed: 0.103 s
% 0.21/0.52  % (22032)------------------------------
% 0.21/0.52  % (22032)------------------------------
% 0.21/0.52  % (22014)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (22014)Refutation not found, incomplete strategy% (22014)------------------------------
% 0.21/0.52  % (22014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22014)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22014)Memory used [KB]: 1663
% 0.21/0.52  % (22014)Time elapsed: 0.090 s
% 0.21/0.52  % (22014)------------------------------
% 0.21/0.52  % (22014)------------------------------
% 0.21/0.53  % (22038)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (22033)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (22016)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (22022)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (22015)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (22044)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (22029)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (22019)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (22036)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (22026)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (22026)Refutation not found, incomplete strategy% (22026)------------------------------
% 0.21/0.54  % (22026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22026)Memory used [KB]: 10618
% 0.21/0.54  % (22026)Time elapsed: 0.136 s
% 0.21/0.54  % (22026)------------------------------
% 0.21/0.54  % (22026)------------------------------
% 0.21/0.54  % (22028)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (22021)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (22034)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (22023)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (22024)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (22017)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  % (22024)Refutation not found, incomplete strategy% (22024)------------------------------
% 0.21/0.55  % (22024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22024)Memory used [KB]: 10618
% 0.21/0.55  % (22024)Time elapsed: 0.136 s
% 0.21/0.55  % (22024)------------------------------
% 0.21/0.55  % (22024)------------------------------
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f126,f178,f187])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ~spl10_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    $false | ~spl10_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f185,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    k1_xboole_0 != sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(flattening,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f6])).
% 0.21/0.55  fof(f6,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    k1_xboole_0 = sK3 | ~spl10_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f184,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    k1_xboole_0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl10_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f183,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl10_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f182,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl10_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f181,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl10_3),
% 0.21/0.55    inference(resolution,[],[f125,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.21/0.55    inference(definition_unfolding,[],[f22,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    ( ! [X14,X12,X13,X11] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14)) | sK4 = k10_mcart_1(X11,X12,X13,X14,sK5) | k1_xboole_0 = X11 | k1_xboole_0 = X12 | k1_xboole_0 = X13 | k1_xboole_0 = X14) ) | ~spl10_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f124])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    spl10_3 <=> ! [X11,X13,X12,X14] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14)) | sK4 = k10_mcart_1(X11,X12,X13,X14,sK5) | k1_xboole_0 = X11 | k1_xboole_0 = X12 | k1_xboole_0 = X13 | k1_xboole_0 = X14)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    ~spl10_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    $false | ~spl10_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f147,f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X1] : (k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) ) | ~spl10_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f111])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    spl10_1 <=> ! [X1] : k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | ~spl10_1),
% 0.21/0.55    inference(superposition,[],[f28,f112])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl10_1 | spl10_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f120,f124,f111])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ( ! [X14,X12,X10,X13,X11] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14)) | k1_xboole_0 = X14 | k1_xboole_0 = X13 | k1_xboole_0 = X12 | k1_xboole_0 = X11 | sK4 = k10_mcart_1(X11,X12,X13,X14,sK5) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X10) )),
% 0.21/0.55    inference(superposition,[],[f62,f109])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(superposition,[],[f95,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X20] : (sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f104,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f89,f24])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f88,f25])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f87,f26])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f86,f27])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(resolution,[],[f60,f46])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f30])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ((((sK7(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f14,f20,f19,f18,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X7 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) => (? [X7] : (? [X8] : (? [X9] : (X4 != X7 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X5,X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (? [X9] : (X4 != X7 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) => (? [X8] : (? [X9] : (sK7(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X5,X4,X3,X2,X1,X0] : (? [X8] : (? [X9] : (sK7(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) => (? [X9] : (sK7(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X5,X4,X3,X2,X1,X0] : (? [X9] : (sK7(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),X9) = X5 & m1_subset_1(X9,X3)) => (sK7(X0,X1,X2,X3,X4,X5) != X4 & k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 & m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X7 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X7 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ( ! [X20] : (sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f103,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f84,f24])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f83,f25])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f82,f26])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f81,f27])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(resolution,[],[f59,f46])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f40,f30])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X20] : (sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f102,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f79,f24])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f78,f25])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f77,f26])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f76,f27])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(resolution,[],[f58,f46])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f41,f30])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ( ! [X20] : (sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f101,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f74,f24])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f73,f25])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f72,f26])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f71,f27])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(resolution,[],[f57,f46])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f42,f30])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X20] : (sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X20] : (sK5 != sK5 | sK4 = sK8(sK0,sK1,sK2,sK3,X20,sK5) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.21/0.55    inference(superposition,[],[f45,f95])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9) | sK4 = X8 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f23,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X6,X8,X7,X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f94,f24])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f93,f25])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f92,f26])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f91,f27])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.55    inference(resolution,[],[f56,f46])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.21/0.55    inference(definition_unfolding,[],[f43,f29,f30])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X7) )),
% 0.21/0.55    inference(equality_resolution,[],[f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f37,f29,f30])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  % (22031)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (22017)------------------------------
% 0.21/0.55  % (22017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22017)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (22017)Memory used [KB]: 10874
% 0.21/0.55  % (22017)Time elapsed: 0.113 s
% 0.21/0.55  % (22017)------------------------------
% 0.21/0.55  % (22017)------------------------------
% 0.21/0.55  % (22030)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (22013)Success in time 0.188 s
%------------------------------------------------------------------------------
