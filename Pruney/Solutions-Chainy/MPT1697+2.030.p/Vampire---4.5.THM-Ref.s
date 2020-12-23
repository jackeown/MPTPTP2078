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
% DateTime   : Thu Dec  3 13:17:31 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  175 (2681 expanded)
%              Number of leaves         :   26 ( 567 expanded)
%              Depth                    :   19
%              Number of atoms          :  655 (24821 expanded)
%              Number of equality atoms :  132 (4446 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f296,f300,f365,f410,f418,f432,f574,f642,f658])).

fof(f658,plain,
    ( spl6_3
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | spl6_3
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f333,f647])).

fof(f647,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_relat_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f646,f439])).

fof(f439,plain,
    ( k3_xboole_0(sK2,sK3) = k1_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(superposition,[],[f181,f433])).

fof(f433,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f312,f431])).

fof(f431,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X1) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl6_12
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f312,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f306,f162])).

fof(f162,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(unit_resulting_resolution,[],[f126,f127,f128,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f128,plain,(
    v4_relat_1(sK5,sK3) ),
    inference(unit_resulting_resolution,[],[f50,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f127,plain,(
    v1_partfun1(sK5,sK3) ),
    inference(unit_resulting_resolution,[],[f59,f48,f49,f50,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f49,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f126,plain,(
    v1_relat_1(sK5) ),
    inference(unit_resulting_resolution,[],[f50,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f306,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK2)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f126,f301,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f301,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f112,f299])).

fof(f299,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X1) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl6_6
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f112,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f57,f54,f56,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f56,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f181,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(sK2,X0) ),
    inference(backward_demodulation,[],[f157,f179])).

fof(f179,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f145,f146,f147,f80])).

fof(f147,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(unit_resulting_resolution,[],[f53,f84])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f146,plain,(
    v1_partfun1(sK4,sK2) ),
    inference(unit_resulting_resolution,[],[f59,f51,f52,f53,f70])).

fof(f52,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f145,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f53,f69])).

fof(f157,plain,(
    ! [X0] : k3_xboole_0(k1_relat_1(sK4),X0) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f145,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f646,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl6_3
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f645,f433])).

fof(f645,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | spl6_3 ),
    inference(forward_demodulation,[],[f176,f180])).

fof(f180,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0)) ),
    inference(backward_demodulation,[],[f156,f179])).

fof(f156,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0)) ),
    inference(unit_resulting_resolution,[],[f145,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f176,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_3
  <=> k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) = k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f333,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_relat_1(k1_xboole_0))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f331,f301])).

fof(f331,plain,
    ( k7_relat_1(sK5,sK2) = k7_relat_1(sK5,k1_relat_1(k1_xboole_0))
    | ~ spl6_6 ),
    inference(superposition,[],[f163,f307])).

fof(f307,plain,
    ( k3_xboole_0(sK3,sK2) = k1_relat_1(k1_xboole_0)
    | ~ spl6_6 ),
    inference(superposition,[],[f164,f301])).

fof(f164,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0) ),
    inference(backward_demodulation,[],[f152,f162])).

fof(f152,plain,(
    ! [X0] : k3_xboole_0(k1_relat_1(sK5),X0) = k1_relat_1(k7_relat_1(sK5,X0)) ),
    inference(unit_resulting_resolution,[],[f126,f77])).

fof(f163,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0)) ),
    inference(backward_demodulation,[],[f151,f162])).

fof(f151,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0)) ),
    inference(unit_resulting_resolution,[],[f126,f76])).

fof(f642,plain,
    ( spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f474,f629,f431])).

fof(f629,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_relat_1(k1_xboole_0))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f628,f333])).

fof(f628,plain,
    ( k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) != k7_relat_1(sK5,k1_relat_1(k1_xboole_0))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f627,f144])).

fof(f144,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    inference(unit_resulting_resolution,[],[f51,f53,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f627,plain,
    ( k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) != k2_partfun1(sK2,sK1,sK4,k1_relat_1(k1_xboole_0))
    | spl6_2
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f626,f439])).

fof(f626,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl6_2 ),
    inference(forward_demodulation,[],[f625,f114])).

fof(f114,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(unit_resulting_resolution,[],[f55,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f625,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_2 ),
    inference(forward_demodulation,[],[f624,f125])).

fof(f125,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ),
    inference(unit_resulting_resolution,[],[f48,f50,f67])).

fof(f624,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f54,f57,f48,f60,f59,f51,f58,f49,f55,f52,f50,f53,f133,f137,f141,f172,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f172,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f141,plain,(
    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    inference(unit_resulting_resolution,[],[f60,f51,f54,f48,f59,f57,f58,f55,f49,f50,f52,f53,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f137,plain,(
    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f59,f51,f54,f60,f48,f57,f58,f55,f49,f50,f52,f53,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,(
    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f59,f51,f54,f60,f48,f57,f58,f55,f49,f50,f52,f53,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f474,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f359,f470,f75])).

fof(f470,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f359,f468,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f468,plain,
    ( r1_xboole_0(sK2,k1_relat_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f465,f179])).

fof(f465,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_relat_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f145,f459,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f459,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_relat_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f456,f421])).

fof(f421,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK3)
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f112,f409])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k9_relat_1(sK4,X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl6_11
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k9_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f456,plain,
    ( k9_relat_1(sK4,sK3) = k9_relat_1(sK4,k1_relat_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(superposition,[],[f272,f439])).

fof(f272,plain,(
    ! [X1] : k9_relat_1(sK4,X1) = k9_relat_1(sK4,k3_xboole_0(sK2,X1)) ),
    inference(forward_demodulation,[],[f268,f158])).

fof(f158,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f145,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f268,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(sK4,X1)) = k9_relat_1(sK4,k3_xboole_0(sK2,X1)) ),
    inference(superposition,[],[f158,f180])).

fof(f359,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl6_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f574,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f474,f555,f431])).

fof(f555,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_relat_1(k1_xboole_0))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f554,f333])).

fof(f554,plain,
    ( k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) != k7_relat_1(sK5,k1_relat_1(k1_xboole_0))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f553,f144])).

fof(f553,plain,
    ( k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) != k2_partfun1(sK2,sK1,sK4,k1_relat_1(k1_xboole_0))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f552,f439])).

fof(f552,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl6_1 ),
    inference(forward_demodulation,[],[f551,f114])).

fof(f551,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(forward_demodulation,[],[f542,f125])).

fof(f542,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f57,f54,f48,f60,f59,f51,f58,f49,f55,f52,f50,f53,f133,f137,f168,f141,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f168,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_1
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f432,plain,
    ( ~ spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f188,f430,f404])).

fof(f404,plain,
    ( spl6_10
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f188,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = k7_relat_1(sK4,X1) ) ),
    inference(superposition,[],[f78,f179])).

fof(f418,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f53,f406,f69])).

fof(f406,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f404])).

fof(f410,plain,
    ( ~ spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f186,f408,f404])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,X0)
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = k9_relat_1(sK4,X0) ) ),
    inference(superposition,[],[f81,f179])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f365,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f83,f360,f69])).

fof(f360,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f358])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f300,plain,
    ( ~ spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f184,f298,f282])).

fof(f282,plain,
    ( spl6_4
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f184,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK3)
      | ~ v1_relat_1(sK5)
      | k1_xboole_0 = k7_relat_1(sK5,X1) ) ),
    inference(superposition,[],[f78,f162])).

fof(f296,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f50,f284,f69])).

fof(f284,plain,
    ( ~ v1_relat_1(sK5)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f282])).

fof(f177,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f150,f174,f170,f166])).

fof(f150,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f131,f144])).

fof(f131,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f116,f125])).

fof(f116,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f47,f114])).

fof(f47,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (1616)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (1608)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (1602)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (1599)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (1593)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (1597)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (1614)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (1620)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (1612)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (1594)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (1603)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (1617)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (1596)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (1623)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.53  % (1598)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.53  % (1618)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.53  % (1595)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.53  % (1607)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.54  % (1604)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.54  % (1606)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.54  % (1610)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (1615)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.54  % (1611)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.54  % (1609)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.54  % (1601)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (1621)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (1622)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.55  % (1616)Refutation not found, incomplete strategy% (1616)------------------------------
% 1.50/0.55  % (1616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (1619)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.55  % (1616)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (1616)Memory used [KB]: 11513
% 1.50/0.55  % (1616)Time elapsed: 0.109 s
% 1.50/0.55  % (1616)------------------------------
% 1.50/0.55  % (1616)------------------------------
% 1.50/0.55  % (1613)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (1600)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.56  % (1611)Refutation not found, incomplete strategy% (1611)------------------------------
% 1.50/0.56  % (1611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (1611)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (1611)Memory used [KB]: 10746
% 1.50/0.56  % (1611)Time elapsed: 0.166 s
% 1.50/0.56  % (1611)------------------------------
% 1.50/0.56  % (1611)------------------------------
% 1.50/0.60  % (1597)Refutation found. Thanks to Tanya!
% 1.50/0.60  % SZS status Theorem for theBenchmark
% 1.50/0.61  % (1603)Refutation not found, incomplete strategy% (1603)------------------------------
% 1.50/0.61  % (1603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (1603)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.61  
% 1.50/0.61  % (1603)Memory used [KB]: 11513
% 1.50/0.61  % (1603)Time elapsed: 0.216 s
% 1.50/0.61  % (1603)------------------------------
% 1.50/0.61  % (1603)------------------------------
% 1.50/0.61  % SZS output start Proof for theBenchmark
% 1.50/0.61  fof(f663,plain,(
% 1.50/0.61    $false),
% 1.50/0.61    inference(avatar_sat_refutation,[],[f177,f296,f300,f365,f410,f418,f432,f574,f642,f658])).
% 1.50/0.61  fof(f658,plain,(
% 1.50/0.61    spl6_3 | ~spl6_6 | ~spl6_12),
% 1.50/0.61    inference(avatar_contradiction_clause,[],[f648])).
% 1.50/0.61  fof(f648,plain,(
% 1.50/0.61    $false | (spl6_3 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f333,f647])).
% 1.50/0.61  fof(f647,plain,(
% 1.50/0.61    k1_xboole_0 != k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) | (spl6_3 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f646,f439])).
% 1.50/0.61  fof(f439,plain,(
% 1.50/0.61    k3_xboole_0(sK2,sK3) = k1_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(superposition,[],[f181,f433])).
% 1.50/0.61  fof(f433,plain,(
% 1.50/0.61    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f312,f431])).
% 1.50/0.61  fof(f431,plain,(
% 1.50/0.61    ( ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1)) ) | ~spl6_12),
% 1.50/0.61    inference(avatar_component_clause,[],[f430])).
% 1.50/0.61  fof(f430,plain,(
% 1.50/0.61    spl6_12 <=> ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1))),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.50/0.61  fof(f312,plain,(
% 1.50/0.61    r1_xboole_0(sK3,sK2) | ~spl6_6),
% 1.50/0.61    inference(forward_demodulation,[],[f306,f162])).
% 1.50/0.61  fof(f162,plain,(
% 1.50/0.61    sK3 = k1_relat_1(sK5)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f126,f127,f128,f80])).
% 1.50/0.61  fof(f80,plain,(
% 1.50/0.61    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f43])).
% 1.50/0.61  fof(f43,plain,(
% 1.50/0.61    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.50/0.61    inference(flattening,[],[f42])).
% 1.50/0.61  fof(f42,plain,(
% 1.50/0.61    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.50/0.61    inference(ennf_transformation,[],[f17])).
% 1.50/0.61  fof(f17,axiom,(
% 1.50/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.50/0.61  fof(f128,plain,(
% 1.50/0.61    v4_relat_1(sK5,sK3)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f50,f84])).
% 1.50/0.61  fof(f84,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f45])).
% 1.50/0.61  fof(f45,plain,(
% 1.50/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.61    inference(ennf_transformation,[],[f15])).
% 1.50/0.61  fof(f15,axiom,(
% 1.50/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.50/0.61  fof(f50,plain,(
% 1.50/0.61    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f24,plain,(
% 1.50/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.50/0.61    inference(flattening,[],[f23])).
% 1.50/0.61  fof(f23,plain,(
% 1.50/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.50/0.61    inference(ennf_transformation,[],[f22])).
% 1.50/0.61  fof(f22,negated_conjecture,(
% 1.50/0.61    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.50/0.61    inference(negated_conjecture,[],[f21])).
% 1.50/0.61  fof(f21,conjecture,(
% 1.50/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.50/0.61  fof(f127,plain,(
% 1.50/0.61    v1_partfun1(sK5,sK3)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f59,f48,f49,f50,f70])).
% 1.50/0.61  fof(f70,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f34])).
% 1.50/0.61  fof(f34,plain,(
% 1.50/0.61    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.50/0.61    inference(flattening,[],[f33])).
% 1.50/0.61  fof(f33,plain,(
% 1.50/0.61    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.50/0.61    inference(ennf_transformation,[],[f16])).
% 1.50/0.61  fof(f16,axiom,(
% 1.50/0.61    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.50/0.61  fof(f49,plain,(
% 1.50/0.61    v1_funct_2(sK5,sK3,sK1)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f48,plain,(
% 1.50/0.61    v1_funct_1(sK5)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f59,plain,(
% 1.50/0.61    ~v1_xboole_0(sK1)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f126,plain,(
% 1.50/0.61    v1_relat_1(sK5)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f50,f69])).
% 1.50/0.61  fof(f69,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f32])).
% 1.50/0.61  fof(f32,plain,(
% 1.50/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.61    inference(ennf_transformation,[],[f14])).
% 1.50/0.61  fof(f14,axiom,(
% 1.50/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.61  fof(f306,plain,(
% 1.50/0.61    r1_xboole_0(k1_relat_1(sK5),sK2) | ~spl6_6),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f126,f301,f75])).
% 1.50/0.61  fof(f75,plain,(
% 1.50/0.61    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f38])).
% 1.50/0.61  fof(f38,plain,(
% 1.50/0.61    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.61    inference(ennf_transformation,[],[f12])).
% 1.50/0.61  fof(f12,axiom,(
% 1.50/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.50/0.61  fof(f301,plain,(
% 1.50/0.61    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_6),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f112,f299])).
% 1.50/0.61  fof(f299,plain,(
% 1.50/0.61    ( ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1)) ) | ~spl6_6),
% 1.50/0.61    inference(avatar_component_clause,[],[f298])).
% 1.50/0.61  fof(f298,plain,(
% 1.50/0.61    spl6_6 <=> ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1))),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.50/0.61  fof(f112,plain,(
% 1.50/0.61    r1_xboole_0(sK2,sK3)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f57,f54,f56,f72])).
% 1.50/0.61  fof(f72,plain,(
% 1.50/0.61    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f36])).
% 1.50/0.61  fof(f36,plain,(
% 1.50/0.61    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.50/0.61    inference(flattening,[],[f35])).
% 1.50/0.61  fof(f35,plain,(
% 1.50/0.61    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.50/0.61    inference(ennf_transformation,[],[f13])).
% 1.50/0.61  fof(f13,axiom,(
% 1.50/0.61    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.50/0.61  fof(f56,plain,(
% 1.50/0.61    r1_subset_1(sK2,sK3)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f54,plain,(
% 1.50/0.61    ~v1_xboole_0(sK3)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f57,plain,(
% 1.50/0.61    ~v1_xboole_0(sK2)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f181,plain,(
% 1.50/0.61    ( ! [X0] : (k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(sK2,X0)) )),
% 1.50/0.61    inference(backward_demodulation,[],[f157,f179])).
% 1.50/0.61  fof(f179,plain,(
% 1.50/0.61    sK2 = k1_relat_1(sK4)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f145,f146,f147,f80])).
% 1.50/0.61  fof(f147,plain,(
% 1.50/0.61    v4_relat_1(sK4,sK2)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f53,f84])).
% 1.50/0.61  fof(f53,plain,(
% 1.50/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f146,plain,(
% 1.50/0.61    v1_partfun1(sK4,sK2)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f59,f51,f52,f53,f70])).
% 1.50/0.61  fof(f52,plain,(
% 1.50/0.61    v1_funct_2(sK4,sK2,sK1)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f51,plain,(
% 1.50/0.61    v1_funct_1(sK4)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f145,plain,(
% 1.50/0.61    v1_relat_1(sK4)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f53,f69])).
% 1.50/0.61  fof(f157,plain,(
% 1.50/0.61    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK4),X0) = k1_relat_1(k7_relat_1(sK4,X0))) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f145,f77])).
% 1.50/0.61  fof(f77,plain,(
% 1.50/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f40])).
% 1.50/0.61  fof(f40,plain,(
% 1.50/0.61    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.50/0.61    inference(ennf_transformation,[],[f11])).
% 1.50/0.61  fof(f11,axiom,(
% 1.50/0.61    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.50/0.61  fof(f646,plain,(
% 1.50/0.61    k1_xboole_0 != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (spl6_3 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f645,f433])).
% 1.50/0.61  fof(f645,plain,(
% 1.50/0.61    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | spl6_3),
% 1.50/0.61    inference(forward_demodulation,[],[f176,f180])).
% 1.50/0.61  fof(f180,plain,(
% 1.50/0.61    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0))) )),
% 1.50/0.61    inference(backward_demodulation,[],[f156,f179])).
% 1.50/0.61  fof(f156,plain,(
% 1.50/0.61    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0))) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f145,f76])).
% 1.50/0.61  fof(f76,plain,(
% 1.50/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f39])).
% 1.50/0.61  fof(f39,plain,(
% 1.50/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.61    inference(ennf_transformation,[],[f9])).
% 1.50/0.61  fof(f9,axiom,(
% 1.50/0.61    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 1.50/0.61  fof(f176,plain,(
% 1.50/0.61    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | spl6_3),
% 1.50/0.61    inference(avatar_component_clause,[],[f174])).
% 1.50/0.61  fof(f174,plain,(
% 1.50/0.61    spl6_3 <=> k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) = k7_relat_1(sK4,k3_xboole_0(sK2,sK3))),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.50/0.61  fof(f333,plain,(
% 1.50/0.61    k1_xboole_0 = k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) | ~spl6_6),
% 1.50/0.61    inference(forward_demodulation,[],[f331,f301])).
% 1.50/0.61  fof(f331,plain,(
% 1.50/0.61    k7_relat_1(sK5,sK2) = k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) | ~spl6_6),
% 1.50/0.61    inference(superposition,[],[f163,f307])).
% 1.50/0.61  fof(f307,plain,(
% 1.50/0.61    k3_xboole_0(sK3,sK2) = k1_relat_1(k1_xboole_0) | ~spl6_6),
% 1.50/0.61    inference(superposition,[],[f164,f301])).
% 1.50/0.61  fof(f164,plain,(
% 1.50/0.61    ( ! [X0] : (k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0)) )),
% 1.50/0.61    inference(backward_demodulation,[],[f152,f162])).
% 1.50/0.61  fof(f152,plain,(
% 1.50/0.61    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK5),X0) = k1_relat_1(k7_relat_1(sK5,X0))) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f126,f77])).
% 1.50/0.61  fof(f163,plain,(
% 1.50/0.61    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0))) )),
% 1.50/0.61    inference(backward_demodulation,[],[f151,f162])).
% 1.50/0.61  fof(f151,plain,(
% 1.50/0.61    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0))) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f126,f76])).
% 1.50/0.61  fof(f642,plain,(
% 1.50/0.61    spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_12),
% 1.50/0.61    inference(avatar_contradiction_clause,[],[f634])).
% 1.50/0.61  fof(f634,plain,(
% 1.50/0.61    $false | (spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_12)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f474,f629,f431])).
% 1.50/0.61  fof(f629,plain,(
% 1.50/0.61    k1_xboole_0 != k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) | (spl6_2 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f628,f333])).
% 1.50/0.61  fof(f628,plain,(
% 1.50/0.61    k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) != k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) | (spl6_2 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f627,f144])).
% 1.50/0.61  fof(f144,plain,(
% 1.50/0.61    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f51,f53,f67])).
% 1.50/0.61  fof(f67,plain,(
% 1.50/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f30])).
% 1.50/0.61  fof(f30,plain,(
% 1.50/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.50/0.61    inference(flattening,[],[f29])).
% 1.50/0.61  fof(f29,plain,(
% 1.50/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.50/0.61    inference(ennf_transformation,[],[f18])).
% 1.50/0.61  fof(f18,axiom,(
% 1.50/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.50/0.61  fof(f627,plain,(
% 1.50/0.61    k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) != k2_partfun1(sK2,sK1,sK4,k1_relat_1(k1_xboole_0)) | (spl6_2 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f626,f439])).
% 1.50/0.61  fof(f626,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl6_2),
% 1.50/0.61    inference(forward_demodulation,[],[f625,f114])).
% 1.50/0.61  fof(f114,plain,(
% 1.50/0.61    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f55,f68])).
% 1.50/0.61  fof(f68,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f31])).
% 1.50/0.61  fof(f31,plain,(
% 1.50/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.50/0.61    inference(ennf_transformation,[],[f1])).
% 1.50/0.61  fof(f1,axiom,(
% 1.50/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.50/0.61  fof(f55,plain,(
% 1.50/0.61    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f625,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_2),
% 1.50/0.61    inference(forward_demodulation,[],[f624,f125])).
% 1.50/0.61  fof(f125,plain,(
% 1.50/0.61    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f48,f50,f67])).
% 1.50/0.61  fof(f624,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_2),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f54,f57,f48,f60,f59,f51,f58,f49,f55,f52,f50,f53,f133,f137,f141,f172,f90])).
% 1.50/0.61  fof(f90,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.50/0.61    inference(equality_resolution,[],[f64])).
% 1.50/0.61  fof(f64,plain,(
% 1.50/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.50/0.61    inference(cnf_transformation,[],[f28])).
% 1.50/0.61  fof(f28,plain,(
% 1.50/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.50/0.61    inference(flattening,[],[f27])).
% 1.50/0.61  fof(f27,plain,(
% 1.50/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.50/0.61    inference(ennf_transformation,[],[f19])).
% 1.50/0.61  fof(f19,axiom,(
% 1.50/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.50/0.61  fof(f172,plain,(
% 1.50/0.61    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_2),
% 1.50/0.61    inference(avatar_component_clause,[],[f170])).
% 1.50/0.61  fof(f170,plain,(
% 1.50/0.61    spl6_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.50/0.61  fof(f141,plain,(
% 1.50/0.61    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f60,f51,f54,f48,f59,f57,f58,f55,f49,f50,f52,f53,f63])).
% 1.50/0.61  fof(f63,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X0)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f26])).
% 1.50/0.61  fof(f26,plain,(
% 1.50/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.50/0.61    inference(flattening,[],[f25])).
% 1.50/0.61  fof(f25,plain,(
% 1.50/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.50/0.61    inference(ennf_transformation,[],[f20])).
% 1.50/0.61  fof(f20,axiom,(
% 1.50/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.50/0.61  fof(f137,plain,(
% 1.50/0.61    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f59,f51,f54,f60,f48,f57,f58,f55,f49,f50,f52,f53,f62])).
% 1.50/0.61  fof(f62,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_xboole_0(X0) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f26])).
% 1.50/0.61  fof(f133,plain,(
% 1.50/0.61    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f59,f51,f54,f60,f48,f57,f58,f55,f49,f50,f52,f53,f61])).
% 1.50/0.61  fof(f61,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_xboole_0(X0) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f26])).
% 1.50/0.61  fof(f58,plain,(
% 1.50/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f60,plain,(
% 1.50/0.61    ~v1_xboole_0(sK0)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  fof(f474,plain,(
% 1.50/0.61    r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_12)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f359,f470,f75])).
% 1.50/0.61  fof(f470,plain,(
% 1.50/0.61    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2) | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_12)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f359,f468,f78])).
% 1.50/0.61  fof(f78,plain,(
% 1.50/0.61    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f41])).
% 1.50/0.61  fof(f41,plain,(
% 1.50/0.61    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.61    inference(ennf_transformation,[],[f8])).
% 1.50/0.61  fof(f8,axiom,(
% 1.50/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 1.50/0.61  fof(f468,plain,(
% 1.50/0.61    r1_xboole_0(sK2,k1_relat_1(k1_xboole_0)) | (~spl6_6 | ~spl6_11 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f465,f179])).
% 1.50/0.61  fof(f465,plain,(
% 1.50/0.61    r1_xboole_0(k1_relat_1(sK4),k1_relat_1(k1_xboole_0)) | (~spl6_6 | ~spl6_11 | ~spl6_12)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f145,f459,f82])).
% 1.50/0.61  fof(f82,plain,(
% 1.50/0.61    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f44])).
% 1.50/0.61  fof(f44,plain,(
% 1.50/0.61    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.61    inference(ennf_transformation,[],[f7])).
% 1.50/0.61  fof(f7,axiom,(
% 1.50/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 1.50/0.61  fof(f459,plain,(
% 1.50/0.61    k1_xboole_0 = k9_relat_1(sK4,k1_relat_1(k1_xboole_0)) | (~spl6_6 | ~spl6_11 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f456,f421])).
% 1.50/0.61  fof(f421,plain,(
% 1.50/0.61    k1_xboole_0 = k9_relat_1(sK4,sK3) | ~spl6_11),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f112,f409])).
% 1.50/0.61  fof(f409,plain,(
% 1.50/0.61    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k9_relat_1(sK4,X0)) ) | ~spl6_11),
% 1.50/0.61    inference(avatar_component_clause,[],[f408])).
% 1.50/0.61  fof(f408,plain,(
% 1.50/0.61    spl6_11 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k9_relat_1(sK4,X0))),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.50/0.61  fof(f456,plain,(
% 1.50/0.61    k9_relat_1(sK4,sK3) = k9_relat_1(sK4,k1_relat_1(k1_xboole_0)) | (~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(superposition,[],[f272,f439])).
% 1.50/0.61  fof(f272,plain,(
% 1.50/0.61    ( ! [X1] : (k9_relat_1(sK4,X1) = k9_relat_1(sK4,k3_xboole_0(sK2,X1))) )),
% 1.50/0.61    inference(forward_demodulation,[],[f268,f158])).
% 1.50/0.61  fof(f158,plain,(
% 1.50/0.61    ( ! [X0] : (k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)) )),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f145,f86])).
% 1.50/0.61  fof(f86,plain,(
% 1.50/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f46])).
% 1.50/0.61  fof(f46,plain,(
% 1.50/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.50/0.61    inference(ennf_transformation,[],[f6])).
% 1.50/0.61  fof(f6,axiom,(
% 1.50/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.50/0.61  fof(f268,plain,(
% 1.50/0.61    ( ! [X1] : (k2_relat_1(k7_relat_1(sK4,X1)) = k9_relat_1(sK4,k3_xboole_0(sK2,X1))) )),
% 1.50/0.61    inference(superposition,[],[f158,f180])).
% 1.50/0.61  fof(f359,plain,(
% 1.50/0.61    v1_relat_1(k1_xboole_0) | ~spl6_8),
% 1.50/0.61    inference(avatar_component_clause,[],[f358])).
% 1.50/0.61  fof(f358,plain,(
% 1.50/0.61    spl6_8 <=> v1_relat_1(k1_xboole_0)),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.50/0.61  fof(f574,plain,(
% 1.50/0.61    spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_12),
% 1.50/0.61    inference(avatar_contradiction_clause,[],[f566])).
% 1.50/0.61  fof(f566,plain,(
% 1.50/0.61    $false | (spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_12)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f474,f555,f431])).
% 1.50/0.61  fof(f555,plain,(
% 1.50/0.61    k1_xboole_0 != k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) | (spl6_1 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f554,f333])).
% 1.50/0.61  fof(f554,plain,(
% 1.50/0.61    k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) != k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) | (spl6_1 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f553,f144])).
% 1.50/0.61  fof(f553,plain,(
% 1.50/0.61    k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) != k2_partfun1(sK2,sK1,sK4,k1_relat_1(k1_xboole_0)) | (spl6_1 | ~spl6_6 | ~spl6_12)),
% 1.50/0.61    inference(forward_demodulation,[],[f552,f439])).
% 1.50/0.61  fof(f552,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl6_1),
% 1.50/0.61    inference(forward_demodulation,[],[f551,f114])).
% 1.50/0.61  fof(f551,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 1.50/0.61    inference(forward_demodulation,[],[f542,f125])).
% 1.50/0.61  fof(f542,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f57,f54,f48,f60,f59,f51,f58,f49,f55,f52,f50,f53,f133,f137,f168,f141,f89])).
% 1.50/0.61  fof(f89,plain,(
% 1.50/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.50/0.61    inference(equality_resolution,[],[f65])).
% 1.50/0.61  fof(f65,plain,(
% 1.50/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.50/0.61    inference(cnf_transformation,[],[f28])).
% 1.50/0.61  fof(f168,plain,(
% 1.50/0.61    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_1),
% 1.50/0.61    inference(avatar_component_clause,[],[f166])).
% 1.50/0.61  fof(f166,plain,(
% 1.50/0.61    spl6_1 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.50/0.61  fof(f432,plain,(
% 1.50/0.61    ~spl6_10 | spl6_12),
% 1.50/0.61    inference(avatar_split_clause,[],[f188,f430,f404])).
% 1.50/0.61  fof(f404,plain,(
% 1.50/0.61    spl6_10 <=> v1_relat_1(sK4)),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.50/0.61  fof(f188,plain,(
% 1.50/0.61    ( ! [X1] : (~r1_xboole_0(X1,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X1)) )),
% 1.50/0.61    inference(superposition,[],[f78,f179])).
% 1.50/0.61  fof(f418,plain,(
% 1.50/0.61    spl6_10),
% 1.50/0.61    inference(avatar_contradiction_clause,[],[f413])).
% 1.50/0.61  fof(f413,plain,(
% 1.50/0.61    $false | spl6_10),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f53,f406,f69])).
% 1.50/0.61  fof(f406,plain,(
% 1.50/0.61    ~v1_relat_1(sK4) | spl6_10),
% 1.50/0.61    inference(avatar_component_clause,[],[f404])).
% 1.50/0.61  fof(f410,plain,(
% 1.50/0.61    ~spl6_10 | spl6_11),
% 1.50/0.61    inference(avatar_split_clause,[],[f186,f408,f404])).
% 1.50/0.61  fof(f186,plain,(
% 1.50/0.61    ( ! [X0] : (~r1_xboole_0(sK2,X0) | ~v1_relat_1(sK4) | k1_xboole_0 = k9_relat_1(sK4,X0)) )),
% 1.50/0.61    inference(superposition,[],[f81,f179])).
% 1.50/0.61  fof(f81,plain,(
% 1.50/0.61    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k9_relat_1(X1,X0)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f44])).
% 1.50/0.61  fof(f365,plain,(
% 1.50/0.61    spl6_8),
% 1.50/0.61    inference(avatar_contradiction_clause,[],[f363])).
% 1.50/0.61  fof(f363,plain,(
% 1.50/0.61    $false | spl6_8),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f83,f360,f69])).
% 1.50/0.61  fof(f360,plain,(
% 1.50/0.61    ~v1_relat_1(k1_xboole_0) | spl6_8),
% 1.50/0.61    inference(avatar_component_clause,[],[f358])).
% 1.50/0.61  fof(f83,plain,(
% 1.50/0.61    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f2])).
% 1.50/0.61  fof(f2,axiom,(
% 1.50/0.61    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.50/0.61  fof(f300,plain,(
% 1.50/0.61    ~spl6_4 | spl6_6),
% 1.50/0.61    inference(avatar_split_clause,[],[f184,f298,f282])).
% 1.50/0.61  fof(f282,plain,(
% 1.50/0.61    spl6_4 <=> v1_relat_1(sK5)),
% 1.50/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.50/0.61  fof(f184,plain,(
% 1.50/0.61    ( ! [X1] : (~r1_xboole_0(X1,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X1)) )),
% 1.50/0.61    inference(superposition,[],[f78,f162])).
% 1.50/0.61  fof(f296,plain,(
% 1.50/0.61    spl6_4),
% 1.50/0.61    inference(avatar_contradiction_clause,[],[f291])).
% 1.50/0.61  fof(f291,plain,(
% 1.50/0.61    $false | spl6_4),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f50,f284,f69])).
% 1.50/0.61  fof(f284,plain,(
% 1.50/0.61    ~v1_relat_1(sK5) | spl6_4),
% 1.50/0.61    inference(avatar_component_clause,[],[f282])).
% 1.50/0.61  fof(f177,plain,(
% 1.50/0.61    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.50/0.61    inference(avatar_split_clause,[],[f150,f174,f170,f166])).
% 1.50/0.61  fof(f150,plain,(
% 1.50/0.61    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.50/0.61    inference(backward_demodulation,[],[f131,f144])).
% 1.50/0.61  fof(f131,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.50/0.61    inference(backward_demodulation,[],[f116,f125])).
% 1.50/0.61  fof(f116,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.50/0.61    inference(backward_demodulation,[],[f47,f114])).
% 1.50/0.61  fof(f47,plain,(
% 1.50/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.50/0.61    inference(cnf_transformation,[],[f24])).
% 1.50/0.61  % SZS output end Proof for theBenchmark
% 1.50/0.61  % (1597)------------------------------
% 1.50/0.61  % (1597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (1597)Termination reason: Refutation
% 1.50/0.61  
% 1.50/0.61  % (1597)Memory used [KB]: 7419
% 1.50/0.61  % (1597)Time elapsed: 0.189 s
% 1.50/0.61  % (1597)------------------------------
% 1.50/0.61  % (1597)------------------------------
% 1.50/0.62  % (1592)Success in time 0.261 s
%------------------------------------------------------------------------------
