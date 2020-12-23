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
% DateTime   : Thu Dec  3 12:59:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 217 expanded)
%              Number of leaves         :   14 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  517 (1061 expanded)
%              Number of equality atoms :  203 ( 479 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f112,f117,f122,f127,f132,f163,f203])).

fof(f203,plain,
    ( spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5
    | spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5
    | spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f201,f56])).

fof(f56,plain,
    ( k1_xboole_0 != sK3
    | spl10_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f201,plain,
    ( k1_xboole_0 = sK3
    | spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_5
    | spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f200,f51])).

fof(f51,plain,
    ( k1_xboole_0 != sK2
    | spl10_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f200,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | spl10_1
    | spl10_2
    | ~ spl10_5
    | spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f199,f46])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f199,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | spl10_1
    | ~ spl10_5
    | spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f198,f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f198,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl10_5
    | spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f197,f111])).

fof(f111,plain,
    ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_6
  <=> sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f197,plain,
    ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(resolution,[],[f176,f61])).

fof(f61,plain,
    ( m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl10_5
  <=> m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f176,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ m1_subset_1(sK5,k4_zfmisc_1(X12,X13,X14,X15))
        | sK4 = k11_mcart_1(X12,X13,X14,X15,sK5)
        | k1_xboole_0 = X12
        | k1_xboole_0 = X13
        | k1_xboole_0 = X14
        | k1_xboole_0 = X15 )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(forward_demodulation,[],[f168,f173])).

fof(f173,plain,
    ( sK4 = sK9(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f172,f131])).

fof(f131,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl10_10
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f172,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f171,f116])).

fof(f116,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl10_7
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f171,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f170,f121])).

fof(f121,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl10_8
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f170,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f169,f126])).

fof(f126,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_9
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f169,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_16 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK9(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_16 ),
    inference(superposition,[],[f13,f162])).

fof(f162,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_16
  <=> sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f13,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X9 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f168,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ m1_subset_1(sK5,k4_zfmisc_1(X12,X13,X14,X15))
        | k1_xboole_0 = X12
        | k1_xboole_0 = X13
        | k1_xboole_0 = X14
        | k1_xboole_0 = X15
        | sK9(sK0,sK1,sK2,sK3,sK5) = k11_mcart_1(X12,X13,X14,X15,sK5) )
    | ~ spl10_16 ),
    inference(superposition,[],[f34,f162])).

fof(f34,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
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

fof(f163,plain,
    ( spl10_16
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f95,f59,f54,f49,f44,f39,f160])).

fof(f95,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f94,f41])).

fof(f94,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f93,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | spl10_2
    | spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f92,f51])).

fof(f92,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | spl10_2
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f68,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))
    | ~ spl10_5 ),
    inference(resolution,[],[f61,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f10])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f132,plain,
    ( spl10_10
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f107,f59,f54,f49,f44,f39,f129])).

fof(f107,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f106,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f105,f56])).

fof(f105,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl10_2
    | spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f104,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl10_2
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f71,f46])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl10_5 ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f127,plain,
    ( spl10_9
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f103,f59,f54,f49,f44,f39,f124])).

fof(f103,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f101,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl10_2
    | spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f100,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl10_2
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f70,f46])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ spl10_5 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f122,plain,
    ( spl10_8
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f99,f59,f54,f49,f44,f39,f119])).

fof(f99,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f97,f56])).

fof(f97,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl10_2
    | spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f96,f51])).

fof(f96,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl10_2
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f69,f46])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ spl10_5 ),
    inference(resolution,[],[f61,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f117,plain,
    ( spl10_7
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f91,f59,f54,f49,f44,f39,f114])).

fof(f91,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f90,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | spl10_2
    | spl10_3
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f89,f56])).

fof(f89,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | spl10_2
    | spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f88,f51])).

fof(f88,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | spl10_2
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f67,f46])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f61,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f112,plain,(
    ~ spl10_6 ),
    inference(avatar_split_clause,[],[f19,f109])).

fof(f19,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f14,f59])).

fof(f14,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f18,f54])).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f17,f49])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f16,f44])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (28515)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % (28538)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.49  % (28530)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (28522)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (28530)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (28533)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (28525)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f112,f117,f122,f127,f132,f163,f203])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5 | spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f202])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    $false | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5 | spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f201,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k1_xboole_0 != sK3 | spl10_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl10_4 <=> k1_xboole_0 = sK3),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | (spl10_1 | spl10_2 | spl10_3 | ~spl10_5 | spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f200,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | spl10_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    spl10_3 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | (spl10_1 | spl10_2 | ~spl10_5 | spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f199,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl10_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl10_2 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | (spl10_1 | ~spl10_5 | spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | spl10_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    spl10_1 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | (~spl10_5 | spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f197,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | spl10_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl10_6 <=> sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | (~spl10_5 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(resolution,[],[f176,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~spl10_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl10_5 <=> m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ( ! [X14,X12,X15,X13] : (~m1_subset_1(sK5,k4_zfmisc_1(X12,X13,X14,X15)) | sK4 = k11_mcart_1(X12,X13,X14,X15,sK5) | k1_xboole_0 = X12 | k1_xboole_0 = X13 | k1_xboole_0 = X14 | k1_xboole_0 = X15) ) | (~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(forward_demodulation,[],[f168,f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    sK4 = sK9(sK0,sK1,sK2,sK3,sK5) | (~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f172,f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | ~spl10_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl10_10 <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) | (~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f171,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~spl10_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl10_7 <=> m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) | (~spl10_8 | ~spl10_9 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f170,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~spl10_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl10_8 <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) | (~spl10_9 | ~spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~spl10_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl10_9 <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) | ~spl10_16),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,sK5) | ~spl10_16),
% 0.21/0.51    inference(superposition,[],[f13,f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | ~spl10_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl10_16 <=> sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X9) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X14,X12,X15,X13] : (~m1_subset_1(sK5,k4_zfmisc_1(X12,X13,X14,X15)) | k1_xboole_0 = X12 | k1_xboole_0 = X13 | k1_xboole_0 = X14 | k1_xboole_0 = X15 | sK9(sK0,sK1,sK2,sK3,sK5) = k11_mcart_1(X12,X13,X14,X15,sK5)) ) | ~spl10_16),
% 0.21/0.51    inference(superposition,[],[f34,f162])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8) )),
% 0.21/0.51    inference(equality_resolution,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl10_16 | spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f95,f59,f54,f49,f44,f39,f160])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f41])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | (spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f56])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | (spl10_2 | spl10_3 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f51])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | (spl10_2 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f46])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f61,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl10_10 | spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f107,f59,f54,f49,f44,f39,f129])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f106,f41])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | (spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f105,f56])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | (spl10_2 | spl10_3 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f51])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | (spl10_2 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f46])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f61,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    spl10_9 | spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f59,f54,f49,f44,f39,f124])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f41])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | (spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f56])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | (spl10_2 | spl10_3 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f51])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | (spl10_2 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f46])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f61,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl10_8 | spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f99,f59,f54,f49,f44,f39,f119])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f41])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | (spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f97,f56])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | (spl10_2 | spl10_3 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f51])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | (spl10_2 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f46])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f61,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl10_7 | spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f91,f59,f54,f49,f44,f39,f114])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f90,f41])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | (spl10_2 | spl10_3 | spl10_4 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f89,f56])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | (spl10_2 | spl10_3 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f51])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | (spl10_2 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f67,f46])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f61,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~spl10_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f19,f109])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl10_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f14,f59])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~spl10_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f18,f54])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    k1_xboole_0 != sK3),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ~spl10_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f17,f49])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    k1_xboole_0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~spl10_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f16,f44])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ~spl10_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f15,f39])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28530)------------------------------
% 0.21/0.51  % (28530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28530)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28530)Memory used [KB]: 10874
% 0.21/0.51  % (28530)Time elapsed: 0.120 s
% 0.21/0.51  % (28530)------------------------------
% 0.21/0.51  % (28530)------------------------------
% 0.21/0.51  % (28517)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (28509)Success in time 0.158 s
%------------------------------------------------------------------------------
