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
% DateTime   : Thu Dec  3 12:59:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 322 expanded)
%              Number of leaves         :   22 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  432 (2287 expanded)
%              Number of equality atoms :  222 (1252 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f134,f136,f139,f141,f143,f155,f158,f161,f164,f198,f200])).

fof(f200,plain,(
    ~ spl10_23 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f26,f197])).

fof(f197,plain,
    ( sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl10_23
  <=> sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f26,plain,(
    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X7
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
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
                           => X4 = X7 ) ) ) ) )
         => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
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
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f198,plain,
    ( spl10_23
    | spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f194,f102,f129,f126,f123,f120,f196])).

fof(f120,plain,
    ( spl10_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f123,plain,
    ( spl10_16
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f126,plain,
    ( spl10_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f129,plain,
    ( spl10_18
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f102,plain,
    ( spl10_10
  <=> sK4 = sK7(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f194,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_10 ),
    inference(resolution,[],[f176,f41])).

fof(f41,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f20,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f20,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f176,plain,
    ( ! [X28,X26,X27,X25] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X25,X26,X27),X28))
        | k1_xboole_0 = X28
        | k1_xboole_0 = X27
        | k1_xboole_0 = X26
        | k1_xboole_0 = X25
        | sK4 = k9_mcart_1(X25,X26,X27,X28,sK5) )
    | ~ spl10_10 ),
    inference(superposition,[],[f53,f168])).

fof(f168,plain,
    ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK4),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f56,f103])).

fof(f103,plain,
    ( sK4 = sK7(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f56,plain,(
    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(global_subsumption,[],[f22,f23,f24,f25,f55])).

fof(f55,plain,
    ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f39,f28])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f10,f18,f17,f16,f15])).

fof(f15,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f25,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f36,f39,f28])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f164,plain,(
    ~ spl10_17 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f24,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f161,plain,(
    ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f25,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f158,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f23,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f155,plain,(
    ~ spl10_15 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f22,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f143,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | ~ spl10_19
    | spl10_8 ),
    inference(avatar_split_clause,[],[f142,f96,f132,f129,f126,f123,f120])).

fof(f132,plain,
    ( spl10_19
  <=> m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f96,plain,
    ( spl10_8
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f142,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_8 ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f141,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | ~ spl10_19
    | spl10_7 ),
    inference(avatar_split_clause,[],[f140,f93,f132,f129,f126,f123,f120])).

fof(f93,plain,
    ( spl10_7
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f140,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_7 ),
    inference(resolution,[],[f94,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f139,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | ~ spl10_19
    | spl10_9 ),
    inference(avatar_split_clause,[],[f138,f99,f132,f129,f126,f123,f120])).

fof(f99,plain,
    ( spl10_9
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f138,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_9 ),
    inference(resolution,[],[f100,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f100,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f136,plain,(
    spl10_19 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl10_19 ),
    inference(subsumption_resolution,[],[f41,f133])).

fof(f133,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | spl10_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl10_15
    | spl10_16
    | spl10_17
    | spl10_18
    | ~ spl10_19
    | spl10_6 ),
    inference(avatar_split_clause,[],[f118,f90,f132,f129,f126,f123,f120])).

fof(f90,plain,
    ( spl10_6
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f118,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_6 ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f104,plain,
    ( ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10 ),
    inference(avatar_split_clause,[],[f72,f102,f99,f96,f93,f90])).

fof(f72,plain,
    ( sK4 = sK7(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,
    ( sK5 != sK5
    | sK4 = sK7(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(superposition,[],[f40,f56])).

fof(f40,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | sK4 = X7
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(definition_unfolding,[],[f21,f39])).

fof(f21,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X7
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:28:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (5512)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (5535)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (5513)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (5512)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (5529)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (5511)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (5519)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (5520)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (5519)Refutation not found, incomplete strategy% (5519)------------------------------
% 0.21/0.52  % (5519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f104,f134,f136,f139,f141,f143,f155,f158,f161,f164,f198,f200])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ~spl10_23),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    $false | ~spl10_23),
% 0.21/0.52    inference(subsumption_resolution,[],[f26,f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | ~spl10_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    spl10_23 <=> sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl10_23 | spl10_15 | spl10_16 | spl10_17 | spl10_18 | ~spl10_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f194,f102,f129,f126,f123,f120,f196])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl10_15 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl10_16 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl10_17 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl10_18 <=> k1_xboole_0 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl10_10 <=> sK4 = sK7(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | ~spl10_10),
% 0.21/0.52    inference(resolution,[],[f176,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ( ! [X28,X26,X27,X25] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X25,X26,X27),X28)) | k1_xboole_0 = X28 | k1_xboole_0 = X27 | k1_xboole_0 = X26 | k1_xboole_0 = X25 | sK4 = k9_mcart_1(X25,X26,X27,X28,sK5)) ) | ~spl10_10),
% 0.21/0.52    inference(superposition,[],[f53,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK4),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) | ~spl10_10),
% 0.21/0.52    inference(forward_demodulation,[],[f56,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    sK4 = sK7(sK0,sK1,sK2,sK3,sK5) | ~spl10_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    inference(global_subsumption,[],[f22,f23,f24,f25,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5)),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f41,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f39,f28])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f10,f18,f17,f16,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f36,f39,f28])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~spl10_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    $false | ~spl10_17),
% 0.21/0.52    inference(subsumption_resolution,[],[f24,f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl10_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~spl10_18),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    $false | ~spl10_18),
% 0.21/0.52    inference(subsumption_resolution,[],[f25,f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | ~spl10_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~spl10_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    $false | ~spl10_16),
% 0.21/0.52    inference(subsumption_resolution,[],[f23,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl10_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~spl10_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    $false | ~spl10_15),
% 0.21/0.52    inference(subsumption_resolution,[],[f22,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl10_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f120])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl10_15 | spl10_16 | spl10_17 | spl10_18 | ~spl10_19 | spl10_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f142,f96,f132,f129,f126,f123,f120])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl10_19 <=> m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl10_8 <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_8),
% 0.21/0.52    inference(resolution,[],[f97,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f28])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | spl10_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    spl10_15 | spl10_16 | spl10_17 | spl10_18 | ~spl10_19 | spl10_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f140,f93,f132,f129,f126,f123,f120])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl10_7 <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_7),
% 0.21/0.52    inference(resolution,[],[f94,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f31,f28])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | spl10_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl10_15 | spl10_16 | spl10_17 | spl10_18 | ~spl10_19 | spl10_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f138,f99,f132,f129,f126,f123,f120])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl10_9 <=> m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_9),
% 0.21/0.52    inference(resolution,[],[f100,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f28])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | spl10_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    spl10_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    $false | spl10_19),
% 0.21/0.52    inference(subsumption_resolution,[],[f41,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | spl10_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl10_15 | spl10_16 | spl10_17 | spl10_18 | ~spl10_19 | spl10_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f118,f90,f132,f129,f126,f123,f120])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl10_6 <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_6),
% 0.21/0.52    inference(resolution,[],[f91,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f28])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | spl10_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f72,f102,f99,f96,f93,f90])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    sK4 = sK7(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    sK5 != sK5 | sK4 = sK7(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    inference(superposition,[],[f40,f56])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | sK4 = X7 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f39])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (sK4 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (5512)------------------------------
% 0.21/0.52  % (5512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5512)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (5512)Memory used [KB]: 10874
% 0.21/0.52  % (5512)Time elapsed: 0.098 s
% 0.21/0.52  % (5512)------------------------------
% 0.21/0.52  % (5512)------------------------------
% 0.21/0.52  % (5525)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (5509)Success in time 0.168 s
%------------------------------------------------------------------------------
