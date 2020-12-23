%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 193 expanded)
%              Number of leaves         :   12 (  56 expanded)
%              Depth                    :   21
%              Number of atoms          :  392 (1330 expanded)
%              Number of equality atoms :  238 ( 782 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f81,f111,f124,f140])).

fof(f140,plain,
    ( spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl10_1
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f55,f70,f65,f60,f75,f80,f136])).

fof(f136,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X8,X9,X10),X11))
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9
        | k1_xboole_0 = X10
        | k1_xboole_0 = X11
        | sK4 = k10_mcart_1(X8,X9,X10,X11,sK5) )
    | ~ spl10_10 ),
    inference(superposition,[],[f49,f123])).

fof(f123,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK4,sK9(sK0,sK1,sK2,sK3,sK5))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl10_10
  <=> sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK4,sK9(sK0,sK1,sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f49,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(definition_unfolding,[],[f32,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
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

fof(f80,plain,
    ( m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl10_6
  <=> m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f75,plain,
    ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | spl10_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl10_5
  <=> sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f65,plain,
    ( k1_xboole_0 != sK2
    | spl10_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f70,plain,
    ( k1_xboole_0 != sK3
    | spl10_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f124,plain,
    ( spl10_1
    | ~ spl10_6
    | spl10_4
    | spl10_3
    | spl10_2
    | spl10_10
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f113,f108,f121,f58,f63,f68,f78,f53])).

fof(f108,plain,
    ( spl10_8
  <=> sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f113,plain,
    ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK4,sK9(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
    | k1_xboole_0 = sK0
    | ~ spl10_8 ),
    inference(superposition,[],[f42,f110])).

fof(f110,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
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

fof(f111,plain,
    ( spl10_8
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f106,f78,f108])).

fof(f106,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_6 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( sK4 = sK8(sK0,sK1,sK2,sK3,sK5)
    | sK5 != sK5
    | ~ spl10_6 ),
    inference(resolution,[],[f100,f80])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0)
      | sK5 != X0 ) ),
    inference(global_subsumption,[],[f15,f16,f17,f18,f99])).

fof(f99,plain,(
    ! [X0] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( sK5 != X0
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f97,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f20])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0)
      | sK5 != X0
      | sK4 = sK8(X1,sK1,sK2,sK3,X0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3))
      | k1_xboole_0 = X1 ) ),
    inference(global_subsumption,[],[f16,f17,f18,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X0)
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0)
      | sK4 = sK8(X1,sK1,sK2,sK3,X0)
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f94,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f20])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1)
      | sK5 != X2
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f17,f18,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1)
      | sK5 != X2
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1)
      | sK5 != X2
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0)
      | sK4 = sK8(X0,X1,sK2,sK3,X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f91,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f20])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2)
      | ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f18,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0)
      | sK4 = sK8(X0,X1,X2,sK3,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f83,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK9(X0,X1,X2,X3,X4),sK3)
      | ~ m1_subset_1(sK7(X0,X1,X2,X3,X4),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,X3,X4),sK2)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,X3,X4),sK0)
      | sK4 = sK8(X0,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f13,f42])).

fof(f13,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X8 ) ),
    inference(cnf_transformation,[],[f8])).

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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
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
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f14,f20])).

fof(f14,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f19,f73])).

fof(f19,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f18,f68])).

fof(f66,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f17,f63])).

fof(f61,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f16,f58])).

fof(f56,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f15,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.54  % (12080)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (12075)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (12096)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (12088)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (12079)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  % (12096)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (12083)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (12086)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.58  % (12091)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f141,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f81,f111,f124,f140])).
% 0.20/0.58  fof(f140,plain,(
% 0.20/0.58    spl10_1 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_6 | ~spl10_10),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.58  fof(f138,plain,(
% 0.20/0.58    $false | (spl10_1 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_6 | ~spl10_10)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f55,f70,f65,f60,f75,f80,f136])).
% 0.20/0.58  fof(f136,plain,(
% 0.20/0.58    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X8,X9,X10),X11)) | k1_xboole_0 = X8 | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11 | sK4 = k10_mcart_1(X8,X9,X10,X11,sK5)) ) | ~spl10_10),
% 0.20/0.58    inference(superposition,[],[f49,f123])).
% 0.20/0.58  fof(f123,plain,(
% 0.20/0.58    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK4,sK9(sK0,sK1,sK2,sK3,sK5)) | ~spl10_10),
% 0.20/0.58    inference(avatar_component_clause,[],[f121])).
% 0.20/0.58  fof(f121,plain,(
% 0.20/0.58    spl10_10 <=> sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK4,sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7) )),
% 0.20/0.58    inference(equality_resolution,[],[f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.20/0.58    inference(definition_unfolding,[],[f32,f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.58    inference(flattening,[],[f11])).
% 0.20/0.58  fof(f11,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | ~spl10_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    spl10_6 <=> m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | spl10_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f73])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    spl10_5 <=> sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    k1_xboole_0 != sK1 | spl10_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    spl10_2 <=> k1_xboole_0 = sK1),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    k1_xboole_0 != sK2 | spl10_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    spl10_3 <=> k1_xboole_0 = sK2),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    k1_xboole_0 != sK3 | spl10_4),
% 0.20/0.58    inference(avatar_component_clause,[],[f68])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    spl10_4 <=> k1_xboole_0 = sK3),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    k1_xboole_0 != sK0 | spl10_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    spl10_1 <=> k1_xboole_0 = sK0),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.58  fof(f124,plain,(
% 0.20/0.58    spl10_1 | ~spl10_6 | spl10_4 | spl10_3 | spl10_2 | spl10_10 | ~spl10_8),
% 0.20/0.58    inference(avatar_split_clause,[],[f113,f108,f121,f58,f63,f68,f78,f53])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    spl10_8 <=> sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK4,sK9(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | ~spl10_8),
% 0.20/0.58    inference(superposition,[],[f42,f110])).
% 0.20/0.58  fof(f110,plain,(
% 0.20/0.58    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | ~spl10_8),
% 0.20/0.58    inference(avatar_component_clause,[],[f108])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f26,f20])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    spl10_8 | ~spl10_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f106,f78,f108])).
% 0.20/0.58  fof(f106,plain,(
% 0.20/0.58    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | ~spl10_6),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f101])).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) | sK5 != sK5 | ~spl10_6),
% 0.20/0.58    inference(resolution,[],[f100,f80])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | sK4 = sK8(sK0,sK1,sK2,sK3,X0) | sK5 != X0) )),
% 0.20/0.58    inference(global_subsumption,[],[f15,f16,f17,f18,f99])).
% 0.20/0.58  fof(f99,plain,(
% 0.20/0.58    ( ! [X0] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f98])).
% 0.20/0.58  fof(f98,plain,(
% 0.20/0.58    ( ! [X0] : (sK5 != X0 | sK4 = sK8(sK0,sK1,sK2,sK3,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0) )),
% 0.20/0.58    inference(resolution,[],[f97,f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f29,f20])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0) | sK5 != X0 | sK4 = sK8(X1,sK1,sK2,sK3,X0) | ~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3)) | k1_xboole_0 = X1) )),
% 0.20/0.58    inference(global_subsumption,[],[f16,f17,f18,f96])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X0) | k1_xboole_0 = sK1 | ~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f95])).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0) | sK4 = sK8(X1,sK1,sK2,sK3,X0) | k1_xboole_0 = sK1 | ~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,sK1,sK2),sK3)) | k1_xboole_0 = X1) )),
% 0.20/0.58    inference(resolution,[],[f94,f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f28,f20])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1) | sK5 != X2 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(global_subsumption,[],[f17,f18,f93])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1) | sK5 != X2 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = sK3) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1) | sK5 != X2 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0) | sK4 = sK8(X0,X1,sK2,sK3,X2) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X2,k2_zfmisc_1(k3_zfmisc_1(X0,X1,sK2),sK3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(resolution,[],[f91,f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f27,f20])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2) | ~m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(global_subsumption,[],[f18,f90])).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f89])).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0) | sK4 = sK8(X0,X1,X2,sK3,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),sK3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(resolution,[],[f83,f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f25,f20])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK9(X0,X1,X2,X3,X4),sK3) | ~m1_subset_1(sK7(X0,X1,X2,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,X3,X4),sK0) | sK4 = sK8(X0,X1,X2,X3,X4) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(superposition,[],[f13,f42])).
% 0.20/0.58  fof(f13,plain,(
% 0.20/0.58    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X8) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,plain,(
% 0.20/0.58    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.58    inference(flattening,[],[f7])).
% 0.20/0.58  fof(f7,plain,(
% 0.20/0.58    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.58    inference(negated_conjecture,[],[f5])).
% 0.20/0.58  fof(f5,conjecture,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    k1_xboole_0 != sK3),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    k1_xboole_0 != sK2),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    k1_xboole_0 != sK1),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    k1_xboole_0 != sK0),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    spl10_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f34,f78])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.20/0.58    inference(definition_unfolding,[],[f14,f20])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ~spl10_5),
% 0.20/0.58    inference(avatar_split_clause,[],[f19,f73])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ~spl10_4),
% 0.20/0.58    inference(avatar_split_clause,[],[f18,f68])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ~spl10_3),
% 0.20/0.58    inference(avatar_split_clause,[],[f17,f63])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    ~spl10_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f16,f58])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ~spl10_1),
% 0.20/0.58    inference(avatar_split_clause,[],[f15,f53])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (12096)------------------------------
% 0.20/0.58  % (12096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (12096)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (12096)Memory used [KB]: 11001
% 0.20/0.58  % (12096)Time elapsed: 0.148 s
% 0.20/0.58  % (12096)------------------------------
% 0.20/0.58  % (12096)------------------------------
% 0.20/0.58  % (12083)Refutation not found, incomplete strategy% (12083)------------------------------
% 0.20/0.58  % (12083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (12073)Success in time 0.227 s
%------------------------------------------------------------------------------
