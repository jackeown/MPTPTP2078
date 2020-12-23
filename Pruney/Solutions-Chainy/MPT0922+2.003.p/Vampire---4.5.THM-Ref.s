%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 313 expanded)
%              Number of leaves         :   25 ( 129 expanded)
%              Depth                    :   10
%              Number of atoms          :  468 (1609 expanded)
%              Number of equality atoms :  221 ( 826 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f95,f102,f109,f116,f170,f188,f190,f193,f197,f200,f229,f232])).

fof(f232,plain,(
    ~ spl11_19 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl11_19 ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( sK5 != sK5
    | ~ spl11_19 ),
    inference(superposition,[],[f32,f228])).

fof(f228,plain,
    ( sK5 = k11_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl11_19
  <=> sK5 = k11_mcart_1(sK1,sK2,sK3,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f32,plain,(
    sK5 != k11_mcart_1(sK1,sK2,sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK5 != k11_mcart_1(sK1,sK2,sK3,sK4,sK6)
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK5 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != sK6
                    | ~ m1_subset_1(X9,sK4) )
                | ~ m1_subset_1(X8,sK3) )
            | ~ m1_subset_1(X7,sK2) )
        | ~ m1_subset_1(X6,sK1) )
    & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X9
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK5 != k11_mcart_1(sK1,sK2,sK3,sK4,sK6)
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK5 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != sK6
                      | ~ m1_subset_1(X9,sK4) )
                  | ~ m1_subset_1(X8,sK3) )
              | ~ m1_subset_1(X7,sK2) )
          | ~ m1_subset_1(X6,sK1) )
      & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

fof(f229,plain,
    ( spl11_2
    | spl11_3
    | spl11_4
    | spl11_5
    | spl11_19
    | ~ spl11_1
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f224,f167,f69,f226,f85,f81,f77,f73])).

fof(f73,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f77,plain,
    ( spl11_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f81,plain,
    ( spl11_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f85,plain,
    ( spl11_5
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f69,plain,
    ( spl11_1
  <=> sK6 = k4_tarski(k4_tarski(k4_tarski(sK10(sK1,sK2,sK3,sK4,sK6),sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f167,plain,
    ( spl11_14
  <=> sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f224,plain,
    ( sK5 = k11_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl11_1
    | ~ spl11_14 ),
    inference(resolution,[],[f203,f50])).

fof(f50,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f26,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f26,plain,(
    m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f203,plain,
    ( ! [X35,X33,X36,X34] :
        ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36))
        | sK5 = k11_mcart_1(X33,X34,X35,X36,sK6)
        | k1_xboole_0 = X36
        | k1_xboole_0 = X35
        | k1_xboole_0 = X34
        | k1_xboole_0 = X33 )
    | ~ spl11_1
    | ~ spl11_14 ),
    inference(backward_demodulation,[],[f127,f169])).

fof(f169,plain,
    ( sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f127,plain,
    ( ! [X35,X33,X36,X34] :
        ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36))
        | k1_xboole_0 = X36
        | k1_xboole_0 = X35
        | k1_xboole_0 = X34
        | k1_xboole_0 = X33
        | sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) = k11_mcart_1(X33,X34,X35,X36,sK6) )
    | ~ spl11_1 ),
    inference(superposition,[],[f58,f71])).

fof(f71,plain,
    ( sK6 = k4_tarski(k4_tarski(k4_tarski(sK10(sK1,sK2,sK3,sK4,sK6),sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f58,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f46,f47,f48])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f200,plain,
    ( spl11_2
    | spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_18
    | spl11_13 ),
    inference(avatar_split_clause,[],[f199,f163,f185,f85,f81,f77,f73])).

fof(f185,plain,
    ( spl11_18
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f163,plain,
    ( spl11_13
  <=> m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f199,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | spl11_13 ),
    inference(resolution,[],[f198,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1)
            & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f15,f24])).

fof(f24,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( sP0(X4,X5,X3,X2,X1)
          & m1_subset_1(X5,X0) )
     => ( sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1)
        & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( sP0(X4,X5,X3,X2,X1)
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f11,f14])).

fof(f14,plain,(
    ! [X4,X5,X3,X2,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
      | ~ sP0(X4,X5,X3,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f198,plain,
    ( ~ sP0(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | spl11_13 ),
    inference(resolution,[],[f165,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X2)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X0
        & m1_subset_1(sK9(X0,X1,X2,X3,X4),X2)
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X4) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( k4_mcart_1(X1,X5,X6,X7) = X0
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X3) )
          & m1_subset_1(X5,X4) )
     => ( ? [X6] :
            ( ? [X7] :
                ( k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),X6,X7) = X0
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X3) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),X6,X7) = X0
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X3) )
     => ( ? [X7] :
            ( k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X7) = X0
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X7) = X0
          & m1_subset_1(X7,X2) )
     => ( k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X0
        & m1_subset_1(sK9(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( k4_mcart_1(X1,X5,X6,X7) = X0
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X3) )
          & m1_subset_1(X5,X4) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X4,X5,X3,X2,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
      | ~ sP0(X4,X5,X3,X2,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f165,plain,
    ( ~ m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f197,plain,
    ( spl11_2
    | spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_18
    | spl11_12 ),
    inference(avatar_split_clause,[],[f196,f159,f185,f85,f81,f77,f73])).

fof(f159,plain,
    ( spl11_12
  <=> m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f196,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | spl11_12 ),
    inference(resolution,[],[f195,f52])).

fof(f195,plain,
    ( ~ sP0(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | spl11_12 ),
    inference(resolution,[],[f161,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f161,plain,
    ( ~ m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f193,plain,
    ( spl11_2
    | spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_18
    | spl11_11 ),
    inference(avatar_split_clause,[],[f192,f155,f185,f85,f81,f77,f73])).

fof(f155,plain,
    ( spl11_11
  <=> m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f192,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | spl11_11 ),
    inference(resolution,[],[f191,f52])).

fof(f191,plain,
    ( ~ sP0(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | spl11_11 ),
    inference(resolution,[],[f157,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X4)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f157,plain,
    ( ~ m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f190,plain,(
    spl11_18 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl11_18 ),
    inference(resolution,[],[f187,f50])).

fof(f187,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))
    | spl11_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f188,plain,
    ( spl11_2
    | spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_18
    | spl11_10 ),
    inference(avatar_split_clause,[],[f183,f151,f185,f85,f81,f77,f73])).

fof(f151,plain,
    ( spl11_10
  <=> m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f183,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | spl11_10 ),
    inference(resolution,[],[f153,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f153,plain,
    ( ~ m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f170,plain,
    ( ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_13
    | spl11_14
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f133,f69,f167,f163,f159,f155,f151])).

fof(f133,plain,
    ( sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | ~ m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | ~ m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2)
    | ~ m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1)
    | ~ spl11_1 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( sK6 != sK6
    | sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | ~ m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | ~ m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2)
    | ~ m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1)
    | ~ spl11_1 ),
    inference(superposition,[],[f49,f71])).

fof(f49,plain,(
    ! [X6,X8,X7,X9] :
      ( sK6 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | sK5 = X9
      | ~ m1_subset_1(X9,sK4)
      | ~ m1_subset_1(X8,sK3)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1) ) ),
    inference(definition_unfolding,[],[f27,f47])).

% (7699)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f27,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 = X9
      | k4_mcart_1(X6,X7,X8,X9) != sK6
      | ~ m1_subset_1(X9,sK4)
      | ~ m1_subset_1(X8,sK3)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    ~ spl11_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl11_5 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl11_5 ),
    inference(superposition,[],[f31,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK4
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f31,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,(
    ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl11_4 ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl11_4 ),
    inference(superposition,[],[f30,f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK3
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f30,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl11_3 ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl11_3 ),
    inference(superposition,[],[f29,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f29,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl11_2 ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl11_2 ),
    inference(superposition,[],[f28,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | spl11_4
    | spl11_5 ),
    inference(avatar_split_clause,[],[f63,f85,f81,f77,f73,f69])).

fof(f63,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | sK6 = k4_tarski(k4_tarski(k4_tarski(sK10(sK1,sK2,sK3,sK4,sK6),sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)) ),
    inference(resolution,[],[f62,f50])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k4_tarski(k4_tarski(k4_tarski(sK10(X1,X2,X3,X4,X0),sK7(X0,sK10(X1,X2,X3,X4,X0),X4,X3,X2)),sK8(X0,sK10(X1,X2,X3,X4,X0),X4,X3,X2)),sK9(X0,sK10(X1,X2,X3,X4,X0),X4,X3,X2)) = X0 ) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | k4_tarski(k4_tarski(k4_tarski(X1,sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X0 ) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X0
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (7710)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (7718)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (7710)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f88,f95,f102,f109,f116,f170,f188,f190,f193,f197,f200,f229,f232])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    ~spl11_19),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    $false | ~spl11_19),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f230])).
% 0.20/0.51  fof(f230,plain,(
% 0.20/0.51    sK5 != sK5 | ~spl11_19),
% 0.20/0.51    inference(superposition,[],[f32,f228])).
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    sK5 = k11_mcart_1(sK1,sK2,sK3,sK4,sK6) | ~spl11_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f226])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    spl11_19 <=> sK5 = k11_mcart_1(sK1,sK2,sK3,sK4,sK6)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    sK5 != k11_mcart_1(sK1,sK2,sK3,sK4,sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    sK5 != k11_mcart_1(sK1,sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK5 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK6 | ~m1_subset_1(X9,sK4)) | ~m1_subset_1(X8,sK3)) | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK5 != k11_mcart_1(sK1,sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK5 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK6 | ~m1_subset_1(X9,sK4)) | ~m1_subset_1(X8,sK3)) | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    spl11_2 | spl11_3 | spl11_4 | spl11_5 | spl11_19 | ~spl11_1 | ~spl11_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f224,f167,f69,f226,f85,f81,f77,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl11_2 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl11_3 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl11_4 <=> k1_xboole_0 = sK3),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl11_5 <=> k1_xboole_0 = sK4),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl11_1 <=> sK6 = k4_tarski(k4_tarski(k4_tarski(sK10(sK1,sK2,sK3,sK4,sK6),sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    spl11_14 <=> sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    sK5 = k11_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | (~spl11_1 | ~spl11_14)),
% 0.20/0.51    inference(resolution,[],[f203,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.20/0.51    inference(definition_unfolding,[],[f26,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    ( ! [X35,X33,X36,X34] : (~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36)) | sK5 = k11_mcart_1(X33,X34,X35,X36,sK6) | k1_xboole_0 = X36 | k1_xboole_0 = X35 | k1_xboole_0 = X34 | k1_xboole_0 = X33) ) | (~spl11_1 | ~spl11_14)),
% 0.20/0.51    inference(backward_demodulation,[],[f127,f169])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | ~spl11_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f167])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ( ! [X35,X33,X36,X34] : (~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X33,X34),X35),X36)) | k1_xboole_0 = X36 | k1_xboole_0 = X35 | k1_xboole_0 = X34 | k1_xboole_0 = X33 | sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) = k11_mcart_1(X33,X34,X35,X36,sK6)) ) | ~spl11_1),
% 0.20/0.51    inference(superposition,[],[f58,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    sK6 = k4_tarski(k4_tarski(k4_tarski(sK10(sK1,sK2,sK3,sK4,sK6),sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)) | ~spl11_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8) )),
% 0.20/0.51    inference(equality_resolution,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f46,f47,f48])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_mcart_1(X5,X6,X7,X8) != X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    spl11_2 | spl11_3 | spl11_4 | spl11_5 | ~spl11_18 | spl11_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f199,f163,f185,f85,f81,f77,f73])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    spl11_18 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    spl11_13 <=> m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | spl11_13),
% 0.20/0.51    inference(resolution,[],[f198,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f42,f48])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (! [X4] : ((sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1) & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f15,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X4,X3,X2,X1,X0] : (? [X5] : (sP0(X4,X5,X3,X2,X1) & m1_subset_1(X5,X0)) => (sP0(X4,sK10(X0,X1,X2,X3,X4),X3,X2,X1) & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (sP0(X4,X5,X3,X2,X1) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.51    inference(definition_folding,[],[f11,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X4,X5,X3,X2,X1] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) | ~sP0(X4,X5,X3,X2,X1))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ~sP0(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | spl11_13),
% 0.20/0.51    inference(resolution,[],[f165,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X2) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : ((((k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X0 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X4)) | ~sP0(X0,X1,X2,X3,X4))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f19,f22,f21,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (k4_mcart_1(X1,X5,X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) & m1_subset_1(X5,X4)) => (? [X6] : (? [X7] : (k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X4)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) => (? [X7] : (k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X4,X3,X2,X1,X0] : (? [X7] : (k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X7) = X0 & m1_subset_1(X7,X2)) => (k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X0 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (k4_mcart_1(X1,X5,X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) & m1_subset_1(X5,X4)) | ~sP0(X0,X1,X2,X3,X4))),
% 0.20/0.51    inference(rectify,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X4,X5,X3,X2,X1] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) | ~sP0(X4,X5,X3,X2,X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f14])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ~m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | spl11_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f163])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    spl11_2 | spl11_3 | spl11_4 | spl11_5 | ~spl11_18 | spl11_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f196,f159,f185,f85,f81,f77,f73])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    spl11_12 <=> m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | spl11_12),
% 0.20/0.51    inference(resolution,[],[f195,f52])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    ~sP0(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | spl11_12),
% 0.20/0.51    inference(resolution,[],[f161,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X3) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ~m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | spl11_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f159])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    spl11_2 | spl11_3 | spl11_4 | spl11_5 | ~spl11_18 | spl11_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f192,f155,f185,f85,f81,f77,f73])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    spl11_11 <=> m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | spl11_11),
% 0.20/0.51    inference(resolution,[],[f191,f52])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~sP0(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | spl11_11),
% 0.20/0.51    inference(resolution,[],[f157,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X4) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ~m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2) | spl11_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f155])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    spl11_18),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    $false | spl11_18),
% 0.20/0.51    inference(resolution,[],[f187,f50])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) | spl11_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f185])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    spl11_2 | spl11_3 | spl11_4 | spl11_5 | ~spl11_18 | spl11_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f183,f151,f185,f85,f81,f77,f73])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl11_10 <=> m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | spl11_10),
% 0.20/0.51    inference(resolution,[],[f153,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f48])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ~m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1) | spl11_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f151])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_13 | spl11_14 | ~spl11_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f133,f69,f167,f163,f159,f155,f151])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | ~m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | ~m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2) | ~m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1) | ~spl11_1),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    sK6 != sK6 | sK5 = sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | ~m1_subset_1(sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | ~m1_subset_1(sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2) | ~m1_subset_1(sK10(sK1,sK2,sK3,sK4,sK6),sK1) | ~spl11_1),
% 0.20/0.51    inference(superposition,[],[f49,f71])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X6,X8,X7,X9] : (sK6 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | sK5 = X9 | ~m1_subset_1(X9,sK4) | ~m1_subset_1(X8,sK3) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f47])).
% 0.20/0.51  % (7699)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X6,X8,X7,X9] : (sK5 = X9 | k4_mcart_1(X6,X7,X8,X9) != sK6 | ~m1_subset_1(X9,sK4) | ~m1_subset_1(X8,sK3) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~spl11_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    $false | ~spl11_5),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~spl11_5),
% 0.20/0.51    inference(superposition,[],[f31,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    k1_xboole_0 = sK4 | ~spl11_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    k1_xboole_0 != sK4),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    ~spl11_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    $false | ~spl11_4),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f107])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~spl11_4),
% 0.20/0.51    inference(superposition,[],[f30,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    k1_xboole_0 = sK3 | ~spl11_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f81])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    k1_xboole_0 != sK3),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~spl11_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    $false | ~spl11_3),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~spl11_3),
% 0.20/0.51    inference(superposition,[],[f29,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl11_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f77])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    k1_xboole_0 != sK2),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ~spl11_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    $false | ~spl11_2),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~spl11_2),
% 0.20/0.51    inference(superposition,[],[f28,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl11_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f73])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    k1_xboole_0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl11_1 | spl11_2 | spl11_3 | spl11_4 | spl11_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f63,f85,f81,f77,f73,f69])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | sK6 = k4_tarski(k4_tarski(k4_tarski(sK10(sK1,sK2,sK3,sK4,sK6),sK7(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK8(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),sK9(sK6,sK10(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2))),
% 0.20/0.51    inference(resolution,[],[f62,f50])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) | k1_xboole_0 = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k4_tarski(k4_tarski(k4_tarski(sK10(X1,X2,X3,X4,X0),sK7(X0,sK10(X1,X2,X3,X4,X0),X4,X3,X2)),sK8(X0,sK10(X1,X2,X3,X4,X0),X4,X3,X2)),sK9(X0,sK10(X1,X2,X3,X4,X0),X4,X3,X2)) = X0) )),
% 0.20/0.51    inference(resolution,[],[f52,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | k4_tarski(k4_tarski(k4_tarski(X1,sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f40,f47])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(X1,sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X0 | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (7710)------------------------------
% 0.20/0.51  % (7710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7710)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (7710)Memory used [KB]: 6652
% 0.20/0.51  % (7710)Time elapsed: 0.086 s
% 0.20/0.51  % (7710)------------------------------
% 0.20/0.51  % (7710)------------------------------
% 0.20/0.51  % (7709)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (7697)Success in time 0.154 s
%------------------------------------------------------------------------------
