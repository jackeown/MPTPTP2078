%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 510 expanded)
%              Number of leaves         :   50 ( 242 expanded)
%              Depth                    :   13
%              Number of atoms          : 1005 (4281 expanded)
%              Number of equality atoms :  140 ( 862 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f871,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f251,f252,f258,f264,f304,f313,f342,f434,f462,f573,f574,f669,f671,f767,f870])).

fof(f870,plain,
    ( ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_21
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(avatar_contradiction_clause,[],[f869])).

fof(f869,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_21
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f868,f257])).

fof(f257,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl11_21
  <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f868,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(forward_demodulation,[],[f867,f263])).

fof(f263,plain,
    ( k1_xboole_0 = k7_relat_1(sK8,k1_xboole_0)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl11_22
  <=> k1_xboole_0 = k7_relat_1(sK8,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f867,plain,
    ( k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(forward_demodulation,[],[f866,f400])).

fof(f400,plain,
    ( ! [X0] : k2_partfun1(sK5,sK4,sK7,X0) = k7_relat_1(sK7,X0)
    | ~ spl11_7
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f137,f127,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f127,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl11_7
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f137,plain,
    ( v1_funct_1(sK7)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl11_9
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f866,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(forward_demodulation,[],[f865,f312])).

fof(f312,plain,
    ( k1_xboole_0 = k3_xboole_0(sK5,sK6)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl11_24
  <=> k1_xboole_0 = k3_xboole_0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f865,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k7_relat_1(sK8,k3_xboole_0(sK5,sK6))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(forward_demodulation,[],[f864,f328])).

fof(f328,plain,
    ( ! [X0] : k9_subset_1(sK3,X0,sK6) = k3_xboole_0(X0,sK6)
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f147,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f147,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl11_11
  <=> m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f864,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(forward_demodulation,[],[f862,f399])).

fof(f399,plain,
    ( ! [X0] : k2_partfun1(sK6,sK4,sK8,X0) = k7_relat_1(sK8,X0)
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f122,f112,f87])).

fof(f112,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_4
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f122,plain,
    ( v1_funct_1(sK8)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl11_6
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f862,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16
    | ~ spl11_30
    | ~ spl11_31
    | spl11_35
    | ~ spl11_51 ),
    inference(unit_resulting_resolution,[],[f172,f167,f162,f137,f152,f122,f157,f147,f132,f117,f127,f112,f413,f572,f417,f766,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | sP1(X4,X0,X2,X1,X6,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( sP1(X4,X0,X2,X1,X6,X3,X5)
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f19,f32,f31])).

fof(f31,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( sP0(X5,X3,X6,X1,X2,X0,X4)
    <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
        & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      <=> sP0(X5,X3,X6,X1,X2,X0,X4) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f766,plain,
    ( v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f764])).

fof(f764,plain,
    ( spl11_51
  <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f417,plain,
    ( m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl11_31
  <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f572,plain,
    ( ~ sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | spl11_35 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl11_35
  <=> sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f413,plain,
    ( v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl11_30
  <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f117,plain,
    ( v1_funct_2(sK8,sK6,sK4)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl11_5
  <=> v1_funct_2(sK8,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f132,plain,
    ( v1_funct_2(sK7,sK5,sK4)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl11_8
  <=> v1_funct_2(sK7,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f157,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl11_13
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK6)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl11_12
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f162,plain,
    ( ~ v1_xboole_0(sK5)
    | spl11_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl11_14
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f167,plain,
    ( ~ v1_xboole_0(sK4)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl11_15
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f172,plain,
    ( ~ v1_xboole_0(sK3)
    | spl11_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl11_16
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f767,plain,
    ( spl11_51
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f761,f458,f764])).

fof(f458,plain,
    ( spl11_34
  <=> sP2(sK4,sK6,sK5,sK3,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f761,plain,
    ( v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | ~ spl11_34 ),
    inference(unit_resulting_resolution,[],[f459,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
        & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
        & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f459,plain,
    ( sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f458])).

fof(f671,plain,
    ( ~ spl11_34
    | spl11_31 ),
    inference(avatar_split_clause,[],[f477,f416,f458])).

fof(f477,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl11_31 ),
    inference(unit_resulting_resolution,[],[f418,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f418,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | spl11_31 ),
    inference(avatar_component_clause,[],[f416])).

fof(f669,plain,
    ( spl11_34
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16 ),
    inference(avatar_split_clause,[],[f613,f170,f165,f160,f155,f150,f145,f135,f130,f125,f120,f115,f110,f458])).

fof(f613,plain,
    ( sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_11
    | spl11_12
    | ~ spl11_13
    | spl11_14
    | spl11_15
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f172,f167,f162,f137,f152,f122,f157,f147,f132,f127,f117,f112,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP2(X1,X3,X2,X0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP2(X1,X3,X2,X0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f30,f34])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f574,plain,
    ( ~ spl11_35
    | spl11_3 ),
    inference(avatar_split_clause,[],[f565,f105,f570])).

fof(f105,plain,
    ( spl11_3
  <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f565,plain,
    ( ~ sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | spl11_3 ),
    inference(unit_resulting_resolution,[],[f470,f93])).

fof(f93,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6)
      | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0)
      | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( ( k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4
          | ~ sP0(X6,X5,X4,X3,X2,X1,X0) )
        & ( sP0(X6,X5,X4,X3,X2,X1,X0)
          | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 ) )
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
          | ~ sP0(X5,X3,X6,X1,X2,X0,X4) )
        & ( sP0(X5,X3,X6,X1,X2,X0,X4)
          | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f470,plain,
    ( ! [X0] : ~ sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0)
    | spl11_3 ),
    inference(unit_resulting_resolution,[],[f107,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6 )
      & ( ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
          & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f107,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f573,plain,
    ( ~ spl11_35
    | spl11_2 ),
    inference(avatar_split_clause,[],[f566,f101,f570])).

fof(f101,plain,
    ( spl11_2
  <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f566,plain,
    ( ~ sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f465,f93])).

fof(f465,plain,
    ( ! [X0] : ~ sP0(X0,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f103,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,
    ( sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f462,plain,
    ( ~ spl11_34
    | spl11_30 ),
    inference(avatar_split_clause,[],[f456,f412,f458])).

fof(f456,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl11_30 ),
    inference(resolution,[],[f414,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f414,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | spl11_30 ),
    inference(avatar_component_clause,[],[f412])).

fof(f434,plain,
    ( ~ spl11_4
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_21
    | ~ spl11_22
    | spl11_25 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_21
    | ~ spl11_22
    | spl11_25 ),
    inference(subsumption_resolution,[],[f432,f257])).

fof(f432,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_22
    | spl11_25 ),
    inference(forward_demodulation,[],[f431,f263])).

fof(f431,plain,
    ( k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_9
    | spl11_25 ),
    inference(forward_demodulation,[],[f430,f400])).

fof(f430,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0)
    | ~ spl11_4
    | ~ spl11_6
    | spl11_25 ),
    inference(subsumption_resolution,[],[f429,f122])).

fof(f429,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0)
    | ~ v1_funct_1(sK8)
    | ~ spl11_4
    | spl11_25 ),
    inference(subsumption_resolution,[],[f403,f112])).

fof(f403,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | spl11_25 ),
    inference(superposition,[],[f338,f87])).

fof(f338,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | spl11_25 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl11_25
  <=> k2_partfun1(sK5,sK4,sK7,k1_xboole_0) = k2_partfun1(sK6,sK4,sK8,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f342,plain,
    ( ~ spl11_25
    | spl11_1
    | ~ spl11_11
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f341,f310,f145,f97,f336])).

fof(f97,plain,
    ( spl11_1
  <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f341,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | spl11_1
    | ~ spl11_11
    | ~ spl11_24 ),
    inference(forward_demodulation,[],[f340,f312])).

fof(f340,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | spl11_1
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f332,f147])).

fof(f332,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | spl11_1 ),
    inference(superposition,[],[f99,f85])).

fof(f99,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f313,plain,
    ( spl11_24
    | ~ spl11_23 ),
    inference(avatar_split_clause,[],[f305,f298,f310])).

fof(f298,plain,
    ( spl11_23
  <=> r1_xboole_0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f305,plain,
    ( k1_xboole_0 = k3_xboole_0(sK5,sK6)
    | ~ spl11_23 ),
    inference(unit_resulting_resolution,[],[f300,f268])).

fof(f268,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f183,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f80,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f22,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f300,plain,
    ( r1_xboole_0(sK5,sK6)
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f298])).

fof(f304,plain,
    ( spl11_23
    | ~ spl11_10
    | spl11_12
    | spl11_14 ),
    inference(avatar_split_clause,[],[f303,f160,f150,f140,f298])).

fof(f140,plain,
    ( spl11_10
  <=> r1_subset_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f303,plain,
    ( r1_xboole_0(sK5,sK6)
    | ~ spl11_10
    | spl11_12
    | spl11_14 ),
    inference(subsumption_resolution,[],[f302,f162])).

fof(f302,plain,
    ( r1_xboole_0(sK5,sK6)
    | v1_xboole_0(sK5)
    | ~ spl11_10
    | spl11_12 ),
    inference(subsumption_resolution,[],[f296,f152])).

fof(f296,plain,
    ( r1_xboole_0(sK5,sK6)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | ~ spl11_10 ),
    inference(resolution,[],[f83,f142])).

fof(f142,plain,
    ( r1_subset_1(sK5,sK6)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f264,plain,
    ( spl11_22
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f259,f247,f261])).

fof(f247,plain,
    ( spl11_20
  <=> v1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f259,plain,
    ( k1_xboole_0 = k7_relat_1(sK8,k1_xboole_0)
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f249,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f249,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f247])).

fof(f258,plain,
    ( spl11_21
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f253,f242,f255])).

fof(f242,plain,
    ( spl11_19
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f253,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0)
    | ~ spl11_19 ),
    inference(unit_resulting_resolution,[],[f244,f77])).

fof(f244,plain,
    ( v1_relat_1(sK7)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f242])).

fof(f252,plain,
    ( spl11_19
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f240,f125,f242])).

fof(f240,plain,
    ( v1_relat_1(sK7)
    | ~ spl11_7 ),
    inference(resolution,[],[f86,f127])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f251,plain,
    ( spl11_20
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f239,f110,f247])).

fof(f239,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_4 ),
    inference(resolution,[],[f86,f112])).

fof(f173,plain,(
    ~ spl11_16 ),
    inference(avatar_split_clause,[],[f55,f170])).

fof(f55,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
      | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
      | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_2(sK8,sK6,sK4)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    & v1_funct_2(sK7,sK5,sK4)
    & v1_funct_1(sK7)
    & r1_subset_1(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & ~ v1_xboole_0(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(sK3))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f16,f41,f40,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                              | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                    & r1_subset_1(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK3))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK3))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X5,X3,X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                    & v1_funct_2(X4,X2,X1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(sK3))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(sK3))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                      & v1_funct_2(X5,X3,sK4)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4)))
                  & v1_funct_2(X4,X2,sK4)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(sK3))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(sK3))
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4
                      | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                    & v1_funct_2(X5,X3,sK4)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4)))
                & v1_funct_2(X4,X2,sK4)
                & v1_funct_1(X4) )
            & r1_subset_1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(sK3))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(sK3))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4
                    | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                  & v1_funct_2(X5,X3,sK4)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
              & v1_funct_2(X4,sK5,sK4)
              & v1_funct_1(X4) )
          & r1_subset_1(sK5,X3)
          & m1_subset_1(X3,k1_zfmisc_1(sK3))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK3))
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5
                  | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4
                  | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                & v1_funct_2(X5,X3,sK4)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
            & v1_funct_2(X4,sK5,sK4)
            & v1_funct_1(X4) )
        & r1_subset_1(sK5,X3)
        & m1_subset_1(X3,k1_zfmisc_1(sK3))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5
                | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4
                | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_2(X5,sK6,sK4)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
          & v1_funct_2(X4,sK5,sK4)
          & v1_funct_1(X4) )
      & r1_subset_1(sK5,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(sK3))
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5
              | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4
              | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
            & v1_funct_2(X5,sK6,sK4)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        & v1_funct_2(X4,sK5,sK4)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5
            | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5)
            | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
          & v1_funct_2(X5,sK6,sK4)
          & v1_funct_1(X5) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      & v1_funct_2(sK7,sK5,sK4)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X5] :
        ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5
          | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5)
          | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
        & v1_funct_2(X5,sK6,sK4)
        & v1_funct_1(X5) )
   => ( ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
        | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
        | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
      & v1_funct_2(sK8,sK6,sK4)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f168,plain,(
    ~ spl11_15 ),
    inference(avatar_split_clause,[],[f56,f165])).

fof(f56,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f163,plain,(
    ~ spl11_14 ),
    inference(avatar_split_clause,[],[f57,f160])).

fof(f57,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f158,plain,(
    spl11_13 ),
    inference(avatar_split_clause,[],[f58,f155])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f153,plain,(
    ~ spl11_12 ),
    inference(avatar_split_clause,[],[f59,f150])).

fof(f59,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f148,plain,(
    spl11_11 ),
    inference(avatar_split_clause,[],[f60,f145])).

fof(f60,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f143,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f61,f140])).

fof(f61,plain,(
    r1_subset_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f62,f135])).

fof(f62,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f63,f130])).

fof(f63,plain,(
    v1_funct_2(sK7,sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f128,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f64,f125])).

fof(f64,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f65,f120])).

fof(f65,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f66,f115])).

fof(f66,plain,(
    v1_funct_2(sK8,sK6,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f67,f110])).

fof(f67,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f68,f105,f101,f97])).

fof(f68,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:29:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (3450)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (3451)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (3440)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (3443)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (3448)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (3447)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3449)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (3436)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3435)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (3438)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (3439)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (3437)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (3436)Refutation not found, incomplete strategy% (3436)------------------------------
% 0.21/0.49  % (3436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3436)Memory used [KB]: 10618
% 0.21/0.49  % (3436)Time elapsed: 0.057 s
% 0.21/0.49  % (3436)------------------------------
% 0.21/0.49  % (3436)------------------------------
% 0.21/0.49  % (3442)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (3441)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (3453)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (3452)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (3444)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (3446)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (3454)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (3445)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (3451)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f871,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f251,f252,f258,f264,f304,f313,f342,f434,f462,f573,f574,f669,f671,f767,f870])).
% 0.21/0.51  fof(f870,plain,(
% 0.21/0.51    ~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_21 | ~spl11_22 | ~spl11_24 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f869])).
% 0.21/0.51  fof(f869,plain,(
% 0.21/0.51    $false | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_21 | ~spl11_22 | ~spl11_24 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51)),
% 0.21/0.51    inference(subsumption_resolution,[],[f868,f257])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0) | ~spl11_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f255])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    spl11_21 <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 0.21/0.51  fof(f868,plain,(
% 0.21/0.51    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_22 | ~spl11_24 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51)),
% 0.21/0.51    inference(forward_demodulation,[],[f867,f263])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK8,k1_xboole_0) | ~spl11_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f261])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    spl11_22 <=> k1_xboole_0 = k7_relat_1(sK8,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 0.21/0.51  fof(f867,plain,(
% 0.21/0.51    k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_24 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51)),
% 0.21/0.51    inference(forward_demodulation,[],[f866,f400])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    ( ! [X0] : (k2_partfun1(sK5,sK4,sK7,X0) = k7_relat_1(sK7,X0)) ) | (~spl11_7 | ~spl11_9)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f137,f127,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~spl11_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl11_7 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    v1_funct_1(sK7) | ~spl11_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl11_9 <=> v1_funct_1(sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.21/0.51  fof(f866,plain,(
% 0.21/0.51    k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0) | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_24 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51)),
% 0.21/0.51    inference(forward_demodulation,[],[f865,f312])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK5,sK6) | ~spl11_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f310])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    spl11_24 <=> k1_xboole_0 = k3_xboole_0(sK5,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 0.21/0.51  fof(f865,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k7_relat_1(sK8,k3_xboole_0(sK5,sK6)) | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51)),
% 0.21/0.51    inference(forward_demodulation,[],[f864,f328])).
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    ( ! [X0] : (k9_subset_1(sK3,X0,sK6) = k3_xboole_0(X0,sK6)) ) | ~spl11_11),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f147,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    m1_subset_1(sK6,k1_zfmisc_1(sK3)) | ~spl11_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl11_11 <=> m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.21/0.51  fof(f864,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51)),
% 0.21/0.51    inference(forward_demodulation,[],[f862,f399])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    ( ! [X0] : (k2_partfun1(sK6,sK4,sK8,X0) = k7_relat_1(sK8,X0)) ) | (~spl11_4 | ~spl11_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f122,f112,f87])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~spl11_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl11_4 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    v1_funct_1(sK8) | ~spl11_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl11_6 <=> v1_funct_1(sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.21/0.51  fof(f862,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16 | ~spl11_30 | ~spl11_31 | spl11_35 | ~spl11_51)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f172,f167,f162,f137,f152,f122,f157,f147,f132,f117,f127,f112,f413,f572,f417,f766,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f19,f32,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X5,X3,X6,X1,X2,X0,X4] : (sP0(X5,X3,X6,X1,X2,X0,X4) <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X4,X0,X2,X1,X6,X3,X5] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X3,X6,X1,X2,X0,X4)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.21/0.51  fof(f766,plain,(
% 0.21/0.51    v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | ~spl11_51),
% 0.21/0.51    inference(avatar_component_clause,[],[f764])).
% 0.21/0.51  fof(f764,plain,(
% 0.21/0.51    spl11_51 <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~spl11_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f416])).
% 0.21/0.51  fof(f416,plain,(
% 0.21/0.51    spl11_31 <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 0.21/0.51  fof(f572,plain,(
% 0.21/0.51    ~sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | spl11_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f570])).
% 0.21/0.51  fof(f570,plain,(
% 0.21/0.51    spl11_35 <=> sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | ~spl11_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f412])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    spl11_30 <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    v1_funct_2(sK8,sK6,sK4) | ~spl11_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl11_5 <=> v1_funct_2(sK8,sK6,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    v1_funct_2(sK7,sK5,sK4) | ~spl11_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f130])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl11_8 <=> v1_funct_2(sK7,sK5,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    m1_subset_1(sK5,k1_zfmisc_1(sK3)) | ~spl11_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl11_13 <=> m1_subset_1(sK5,k1_zfmisc_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~v1_xboole_0(sK6) | spl11_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl11_12 <=> v1_xboole_0(sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ~v1_xboole_0(sK5) | spl11_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl11_14 <=> v1_xboole_0(sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~v1_xboole_0(sK4) | spl11_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl11_15 <=> v1_xboole_0(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~v1_xboole_0(sK3) | spl11_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    spl11_16 <=> v1_xboole_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.21/0.51  fof(f767,plain,(
% 0.21/0.51    spl11_51 | ~spl11_34),
% 0.21/0.51    inference(avatar_split_clause,[],[f761,f458,f764])).
% 0.21/0.51  fof(f458,plain,(
% 0.21/0.51    spl11_34 <=> sP2(sK4,sK6,sK5,sK3,sK8,sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 0.21/0.51  fof(f761,plain,(
% 0.21/0.51    v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | ~spl11_34),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f459,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP2(X0,X1,X2,X3,X4,X5))),
% 0.21/0.51    inference(rectify,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 0.21/0.51    inference(nnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f459,plain,(
% 0.21/0.51    sP2(sK4,sK6,sK5,sK3,sK8,sK7) | ~spl11_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f458])).
% 0.21/0.51  fof(f671,plain,(
% 0.21/0.51    ~spl11_34 | spl11_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f477,f416,f458])).
% 0.21/0.51  fof(f477,plain,(
% 0.21/0.51    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl11_31),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f418,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f54])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    ~m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | spl11_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f416])).
% 0.21/0.51  fof(f669,plain,(
% 0.21/0.51    spl11_34 | ~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f613,f170,f165,f160,f155,f150,f145,f135,f130,f125,f120,f115,f110,f458])).
% 0.21/0.51  fof(f613,plain,(
% 0.21/0.51    sP2(sK4,sK6,sK5,sK3,sK8,sK7) | (~spl11_4 | ~spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | ~spl11_9 | ~spl11_11 | spl11_12 | ~spl11_13 | spl11_14 | spl11_15 | spl11_16)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f172,f167,f162,f137,f152,f122,f157,f147,f132,f127,f117,f112,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f30,f34])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.21/0.51  fof(f574,plain,(
% 0.21/0.51    ~spl11_35 | spl11_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f565,f105,f570])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl11_3 <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.51  fof(f565,plain,(
% 0.21/0.51    ~sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | spl11_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f470,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X6,X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6) | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : (((k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4 | ~sP0(X6,X5,X4,X3,X2,X1,X0)) & (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4)) | ~sP1(X0,X1,X2,X3,X4,X5,X6))),
% 0.21/0.51    inference(rectify,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X4,X0,X2,X1,X6,X3,X5] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X3,X6,X1,X2,X0,X4)) & (sP0(X5,X3,X6,X1,X2,X0,X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 0.21/0.51    inference(nnf_transformation,[],[f32])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0)) ) | spl11_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f107,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0 | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6) & ((k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 0.21/0.51    inference(rectify,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 0.21/0.51    inference(flattening,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 0.21/0.51    inference(nnf_transformation,[],[f31])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | spl11_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f573,plain,(
% 0.21/0.51    ~spl11_35 | spl11_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f566,f101,f570])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl11_2 <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.51  fof(f566,plain,(
% 0.21/0.51    ~sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | spl11_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f465,f93])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(X0,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)) ) | spl11_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f103,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | spl11_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    ~spl11_34 | spl11_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f456,f412,f458])).
% 0.21/0.51  fof(f456,plain,(
% 0.21/0.51    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl11_30),
% 0.21/0.51    inference(resolution,[],[f414,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f54])).
% 0.21/0.51  fof(f414,plain,(
% 0.21/0.51    ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | spl11_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f412])).
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    ~spl11_4 | ~spl11_6 | ~spl11_7 | ~spl11_9 | ~spl11_21 | ~spl11_22 | spl11_25),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f433])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    $false | (~spl11_4 | ~spl11_6 | ~spl11_7 | ~spl11_9 | ~spl11_21 | ~spl11_22 | spl11_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f432,f257])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | (~spl11_4 | ~spl11_6 | ~spl11_7 | ~spl11_9 | ~spl11_22 | spl11_25)),
% 0.21/0.51    inference(forward_demodulation,[],[f431,f263])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    k7_relat_1(sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | (~spl11_4 | ~spl11_6 | ~spl11_7 | ~spl11_9 | spl11_25)),
% 0.21/0.51    inference(forward_demodulation,[],[f430,f400])).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0) | (~spl11_4 | ~spl11_6 | spl11_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f429,f122])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0) | ~v1_funct_1(sK8) | (~spl11_4 | spl11_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f403,f112])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    k7_relat_1(sK8,k1_xboole_0) != k2_partfun1(sK5,sK4,sK7,k1_xboole_0) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | spl11_25),
% 0.21/0.51    inference(superposition,[],[f338,f87])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | spl11_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f336])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    spl11_25 <=> k2_partfun1(sK5,sK4,sK7,k1_xboole_0) = k2_partfun1(sK6,sK4,sK8,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    ~spl11_25 | spl11_1 | ~spl11_11 | ~spl11_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f341,f310,f145,f97,f336])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl11_1 <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | (spl11_1 | ~spl11_11 | ~spl11_24)),
% 0.21/0.51    inference(forward_demodulation,[],[f340,f312])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | (spl11_1 | ~spl11_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f332,f147])).
% 0.21/0.51  fof(f332,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | spl11_1),
% 0.21/0.51    inference(superposition,[],[f99,f85])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | spl11_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    spl11_24 | ~spl11_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f305,f298,f310])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    spl11_23 <=> r1_xboole_0(sK5,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK5,sK6) | ~spl11_23),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f300,f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f183,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),X2) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f80,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f22,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    r1_xboole_0(sK5,sK6) | ~spl11_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f298])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    spl11_23 | ~spl11_10 | spl11_12 | spl11_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f303,f160,f150,f140,f298])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl11_10 <=> r1_subset_1(sK5,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    r1_xboole_0(sK5,sK6) | (~spl11_10 | spl11_12 | spl11_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f302,f162])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    r1_xboole_0(sK5,sK6) | v1_xboole_0(sK5) | (~spl11_10 | spl11_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f296,f152])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    r1_xboole_0(sK5,sK6) | v1_xboole_0(sK6) | v1_xboole_0(sK5) | ~spl11_10),
% 0.21/0.51    inference(resolution,[],[f83,f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    r1_subset_1(sK5,sK6) | ~spl11_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f140])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    spl11_22 | ~spl11_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f259,f247,f261])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl11_20 <=> v1_relat_1(sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK8,k1_xboole_0) | ~spl11_20),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f249,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    v1_relat_1(sK8) | ~spl11_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f247])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    spl11_21 | ~spl11_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f253,f242,f255])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    spl11_19 <=> v1_relat_1(sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0) | ~spl11_19),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f244,f77])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    v1_relat_1(sK7) | ~spl11_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f242])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    spl11_19 | ~spl11_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f240,f125,f242])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    v1_relat_1(sK7) | ~spl11_7),
% 0.21/0.51    inference(resolution,[],[f86,f127])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    spl11_20 | ~spl11_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f239,f110,f247])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    v1_relat_1(sK8) | ~spl11_4),
% 0.21/0.51    inference(resolution,[],[f86,f112])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~spl11_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f170])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~v1_xboole_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ((((((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f16,f41,f40,f39,f38,f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) => ((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~spl11_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f165])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~v1_xboole_0(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~spl11_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f160])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~v1_xboole_0(sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    spl11_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f58,f155])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    m1_subset_1(sK5,k1_zfmisc_1(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~spl11_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f59,f150])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~v1_xboole_0(sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl11_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f145])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl11_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f61,f140])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    r1_subset_1(sK5,sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl11_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f62,f135])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    v1_funct_1(sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl11_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f63,f130])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    v1_funct_2(sK7,sK5,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl11_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f64,f125])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl11_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f65,f120])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    v1_funct_1(sK8)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl11_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f115])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    v1_funct_2(sK8,sK6,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl11_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f67,f110])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~spl11_1 | ~spl11_2 | ~spl11_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f105,f101,f97])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (3451)------------------------------
% 0.21/0.51  % (3451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3451)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (3451)Memory used [KB]: 11641
% 0.21/0.51  % (3451)Time elapsed: 0.088 s
% 0.21/0.51  % (3451)------------------------------
% 0.21/0.51  % (3451)------------------------------
% 0.21/0.51  % (3434)Success in time 0.156 s
%------------------------------------------------------------------------------
