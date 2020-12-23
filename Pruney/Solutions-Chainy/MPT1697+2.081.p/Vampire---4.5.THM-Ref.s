%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  263 ( 620 expanded)
%              Number of leaves         :   42 ( 232 expanded)
%              Depth                    :   28
%              Number of atoms          : 1964 (3571 expanded)
%              Number of equality atoms :  168 ( 402 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f96,f103,f107,f113,f117,f121,f154,f158,f162,f175,f195,f199,f204,f208,f218,f222,f237,f335,f368,f384,f400,f570,f593,f601])).

fof(f601,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_21
    | ~ spl6_27
    | ~ spl6_37 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_21
    | ~ spl6_27
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f599,f236])).

fof(f236,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl6_27
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f599,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_21
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f598,f334])).

fof(f334,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl6_37
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f598,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_21 ),
    inference(forward_demodulation,[],[f597,f183])).

fof(f183,plain,
    ( ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f177,f75])).

fof(f75,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_2
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) )
    | ~ spl6_16 ),
    inference(resolution,[],[f157,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f157,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f597,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_17
    | spl6_21 ),
    inference(forward_demodulation,[],[f596,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_17
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f596,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_15
    | spl6_21 ),
    inference(forward_demodulation,[],[f595,f123])).

fof(f123,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f116,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f595,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_15
    | spl6_21 ),
    inference(forward_demodulation,[],[f194,f170])).

fof(f170,plain,
    ( ! [X0] : k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f164,f71])).

fof(f71,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK5)
        | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) )
    | ~ spl6_15 ),
    inference(resolution,[],[f153,f53])).

fof(f153,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_15
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f194,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_21
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f593,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_27
    | ~ spl6_37
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_27
    | ~ spl6_37
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f191,f548])).

fof(f548,plain,
    ( sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_27
    | ~ spl6_37
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f547,f236])).

fof(f547,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_37
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f546,f334])).

fof(f546,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f545,f183])).

fof(f545,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f544,f161])).

fof(f544,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f543,f123])).

fof(f543,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f542,f170])).

fof(f542,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f541,f91])).

fof(f91,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f541,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f540,f383])).

fof(f383,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl6_44
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f540,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f539,f367])).

fof(f367,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl6_40
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f539,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f538,f153])).

fof(f538,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f537,f106])).

fof(f106,plain,
    ( v1_funct_2(sK5,sK3,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_9
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f537,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f536,f71])).

fof(f536,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f535,f157])).

fof(f535,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f534,f112])).

fof(f112,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_10
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f534,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f533,f75])).

fof(f533,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f532,f116])).

fof(f532,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f531,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_3
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f531,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_4
    | spl6_5
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f530,f120])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f530,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_4
    | spl6_5
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f529,f83])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f529,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_5
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f514,f87])).

fof(f87,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f514,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_48 ),
    inference(resolution,[],[f399,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
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
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f399,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl6_48
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f191,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_20
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f570,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_19
    | ~ spl6_27
    | ~ spl6_37
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_19
    | ~ spl6_27
    | ~ spl6_37
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f568,f236])).

fof(f568,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_19
    | ~ spl6_37
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f567,f334])).

fof(f567,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_19
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f566,f183])).

fof(f566,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_19
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f565,f161])).

fof(f565,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | spl6_19
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f564,f123])).

fof(f564,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | spl6_19
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f563,f170])).

fof(f563,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | spl6_19
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f562,f188])).

fof(f188,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_19
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f562,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f561,f91])).

fof(f561,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f560,f383])).

fof(f560,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_40
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f559,f367])).

fof(f559,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f558,f153])).

fof(f558,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f557,f106])).

fof(f557,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f556,f71])).

fof(f556,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f555,f157])).

fof(f555,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f554,f112])).

fof(f554,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f553,f75])).

fof(f553,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f552,f116])).

fof(f552,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f551,f79])).

fof(f551,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_4
    | spl6_5
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f550,f120])).

fof(f550,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_4
    | spl6_5
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f549,f83])).

fof(f549,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_5
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f515,f87])).

fof(f515,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_48 ),
    inference(resolution,[],[f399,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
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
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f400,plain,
    ( spl6_48
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f352,f156,f152,f119,f115,f111,f105,f90,f86,f82,f78,f74,f70,f398])).

fof(f352,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f351,f79])).

fof(f351,plain,
    ( v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f350,f106])).

fof(f350,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f349,f71])).

fof(f349,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f347,f116])).

fof(f347,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f258,f153])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | v1_xboole_0(X0)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1))) )
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f257,f87])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1))) )
    | ~ spl6_2
    | spl6_4
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f256,f112])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_2(sK4,sK2,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1))) )
    | ~ spl6_2
    | spl6_4
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f255,f75])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,sK2,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1))) )
    | spl6_4
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f143,f157])).

fof(f143,plain,
    ( ! [X12,X10,X11,X9] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9)))
        | v1_xboole_0(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,sK2,X9)
        | v1_xboole_0(X9)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X9)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
        | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9))) )
    | spl6_4
    | spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f142,f91])).

fof(f142,plain,
    ( ! [X12,X10,X11,X9] :
        ( v1_xboole_0(X9)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,sK2,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9)))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X9)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
        | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9))) )
    | spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f137,f83])).

fof(f137,plain,
    ( ! [X12,X10,X11,X9] :
        ( v1_xboole_0(X9)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,sK2,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9)))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X9)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
        | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9))) )
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f384,plain,
    ( spl6_44
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f327,f156,f152,f119,f115,f111,f105,f90,f86,f82,f78,f74,f70,f382])).

fof(f327,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f326,f79])).

fof(f326,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f325,f106])).

fof(f325,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f324,f71])).

fof(f324,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f322,f116])).

fof(f322,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f246,f153])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | v1_xboole_0(X0)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1) )
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f245,f87])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1) )
    | ~ spl6_2
    | spl6_4
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f244,f112])).

% (19727)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f244,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_2(sK4,sK2,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1) )
    | ~ spl6_2
    | spl6_4
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f243,f75])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,sK2,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1) )
    | spl6_4
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f141,f157])).

fof(f141,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5)))
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,sK2,X5)
        | v1_xboole_0(X5)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5) )
    | spl6_4
    | spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f140,f91])).

fof(f140,plain,
    ( ! [X6,X8,X7,X5] :
        ( v1_xboole_0(X5)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,sK2,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5)))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5) )
    | spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f136,f83])).

fof(f136,plain,
    ( ! [X6,X8,X7,X5] :
        ( v1_xboole_0(X5)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,sK2,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5)))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5) )
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f368,plain,
    ( spl6_40
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f305,f156,f152,f119,f115,f111,f105,f90,f86,f82,f78,f74,f70,f366])).

fof(f305,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f304,f79])).

fof(f304,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f303,f106])).

fof(f303,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f302,f71])).

fof(f302,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f300,f116])).

fof(f300,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f233,f153])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | v1_xboole_0(X0)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1)) )
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f232,f87])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1)) )
    | ~ spl6_2
    | spl6_4
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f231,f112])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_2(sK4,sK2,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1)) )
    | ~ spl6_2
    | spl6_4
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f230,f75])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,sK2,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1)) )
    | spl6_4
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f139,f157])).

fof(f139,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK2,X1)
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X2,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4)) )
    | spl6_4
    | spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f138,f91])).

fof(f138,plain,
    ( ! [X4,X2,X3,X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X2,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4)) )
    | spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f135,f83])).

fof(f135,plain,
    ( ! [X4,X2,X3,X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X2,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f335,plain,
    ( spl6_37
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f320,f220,f197,f333])).

fof(f197,plain,
    ( spl6_22
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f220,plain,
    ( spl6_26
  <=> sK4 = k7_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f320,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(superposition,[],[f283,f221])).

fof(f221,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f220])).

fof(f283,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)
    | ~ spl6_22 ),
    inference(resolution,[],[f200,f63])).

fof(f63,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),X1) )
    | ~ spl6_22 ),
    inference(resolution,[],[f198,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f198,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f197])).

fof(f237,plain,
    ( spl6_27
    | ~ spl6_18
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f229,f216,f173,f235])).

fof(f173,plain,
    ( spl6_18
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f216,plain,
    ( spl6_25
  <=> sK5 = k7_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f229,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_18
    | ~ spl6_25 ),
    inference(superposition,[],[f223,f217])).

fof(f217,plain,
    ( sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f223,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0)
    | ~ spl6_18 ),
    inference(resolution,[],[f185,f63])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),X1) )
    | ~ spl6_18 ),
    inference(resolution,[],[f174,f59])).

fof(f174,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f222,plain,
    ( spl6_26
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f212,f206,f197,f220])).

fof(f206,plain,
    ( spl6_24
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f212,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f211,f198])).

fof(f211,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_24 ),
    inference(resolution,[],[f207,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f207,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f218,plain,
    ( spl6_25
    | ~ spl6_18
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f210,f202,f173,f216])).

fof(f202,plain,
    ( spl6_23
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f210,plain,
    ( sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_18
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f209,f174])).

fof(f209,plain,
    ( ~ v1_relat_1(sK5)
    | sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_23 ),
    inference(resolution,[],[f203,f60])).

fof(f203,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f202])).

fof(f208,plain,
    ( spl6_24
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f176,f156,f206])).

fof(f176,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f157,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f204,plain,
    ( spl6_23
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f163,f152,f202])).

fof(f163,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_15 ),
    inference(resolution,[],[f153,f64])).

fof(f199,plain,
    ( spl6_22
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f184,f156,f197])).

fof(f184,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f178,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f178,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4)
    | ~ spl6_16 ),
    inference(resolution,[],[f157,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f195,plain,
    ( ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f33,f193,f190,f187])).

fof(f33,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f175,plain,
    ( spl6_18
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f171,f152,f173])).

fof(f171,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f165,f55])).

fof(f165,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5)
    | ~ spl6_15 ),
    inference(resolution,[],[f153,f58])).

fof(f162,plain,
    ( spl6_17
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f108,f101,f160])).

fof(f101,plain,
    ( spl6_8
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f108,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f102,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f102,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f158,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f39,f156])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f154,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f36,f152])).

fof(f36,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f44,f119])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f41,f115])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f38,f111])).

fof(f38,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f35,f105])).

fof(f35,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,
    ( spl6_8
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f99,f94,f82,f78,f101])).

fof(f94,plain,
    ( spl6_7
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f99,plain,
    ( r1_xboole_0(sK2,sK3)
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f98,f83])).

fof(f98,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f97,f79])).

fof(f97,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f95,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f95,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f46,f90])).

fof(f46,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f45,f86])).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f34,f70])).

fof(f34,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:53:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (19745)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (19735)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.45  % (19725)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (19739)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.47  % (19745)Refutation not found, incomplete strategy% (19745)------------------------------
% 0.19/0.47  % (19745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (19745)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (19745)Memory used [KB]: 10618
% 0.19/0.47  % (19745)Time elapsed: 0.075 s
% 0.19/0.47  % (19745)------------------------------
% 0.19/0.47  % (19745)------------------------------
% 0.19/0.47  % (19738)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (19736)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.47  % (19731)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (19733)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  % (19732)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (19730)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (19734)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.48  % (19729)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.48  % (19725)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f602,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f96,f103,f107,f113,f117,f121,f154,f158,f162,f175,f195,f199,f204,f208,f218,f222,f237,f335,f368,f384,f400,f570,f593,f601])).
% 0.19/0.48  fof(f601,plain,(
% 0.19/0.48    ~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_21 | ~spl6_27 | ~spl6_37),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f600])).
% 0.19/0.48  fof(f600,plain,(
% 0.19/0.48    $false | (~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_21 | ~spl6_27 | ~spl6_37)),
% 0.19/0.48    inference(subsumption_resolution,[],[f599,f236])).
% 0.19/0.48  fof(f236,plain,(
% 0.19/0.48    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_27),
% 0.19/0.48    inference(avatar_component_clause,[],[f235])).
% 0.19/0.48  fof(f235,plain,(
% 0.19/0.48    spl6_27 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.19/0.48  fof(f599,plain,(
% 0.19/0.48    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_21 | ~spl6_37)),
% 0.19/0.48    inference(forward_demodulation,[],[f598,f334])).
% 0.19/0.48  fof(f334,plain,(
% 0.19/0.48    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_37),
% 0.19/0.48    inference(avatar_component_clause,[],[f333])).
% 0.19/0.48  fof(f333,plain,(
% 0.19/0.48    spl6_37 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.19/0.48  fof(f598,plain,(
% 0.19/0.48    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_21)),
% 0.19/0.48    inference(forward_demodulation,[],[f597,f183])).
% 0.19/0.48  fof(f183,plain,(
% 0.19/0.48    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl6_2 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f177,f75])).
% 0.19/0.48  fof(f75,plain,(
% 0.19/0.48    v1_funct_1(sK4) | ~spl6_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f74])).
% 0.19/0.48  fof(f74,plain,(
% 0.19/0.48    spl6_2 <=> v1_funct_1(sK4)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.48  fof(f177,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_funct_1(sK4) | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | ~spl6_16),
% 0.19/0.48    inference(resolution,[],[f157,f53])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.48    inference(flattening,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.19/0.48  fof(f157,plain,(
% 0.19/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_16),
% 0.19/0.48    inference(avatar_component_clause,[],[f156])).
% 0.19/0.48  fof(f156,plain,(
% 0.19/0.48    spl6_16 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.19/0.48  fof(f597,plain,(
% 0.19/0.48    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_1 | ~spl6_11 | ~spl6_15 | ~spl6_17 | spl6_21)),
% 0.19/0.48    inference(forward_demodulation,[],[f596,f161])).
% 0.19/0.48  fof(f161,plain,(
% 0.19/0.48    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_17),
% 0.19/0.48    inference(avatar_component_clause,[],[f160])).
% 0.19/0.48  fof(f160,plain,(
% 0.19/0.48    spl6_17 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.19/0.48  fof(f596,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_11 | ~spl6_15 | spl6_21)),
% 0.19/0.48    inference(forward_demodulation,[],[f595,f123])).
% 0.19/0.48  fof(f123,plain,(
% 0.19/0.48    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) ) | ~spl6_11),
% 0.19/0.48    inference(resolution,[],[f116,f54])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f115])).
% 0.19/0.48  fof(f115,plain,(
% 0.19/0.48    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.48  fof(f595,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_15 | spl6_21)),
% 0.19/0.48    inference(forward_demodulation,[],[f194,f170])).
% 0.19/0.48  fof(f170,plain,(
% 0.19/0.48    ( ! [X0] : (k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | (~spl6_1 | ~spl6_15)),
% 0.19/0.48    inference(subsumption_resolution,[],[f164,f71])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    v1_funct_1(sK5) | ~spl6_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f70])).
% 0.19/0.48  fof(f70,plain,(
% 0.19/0.48    spl6_1 <=> v1_funct_1(sK5)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.48  fof(f164,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_funct_1(sK5) | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | ~spl6_15),
% 0.19/0.48    inference(resolution,[],[f153,f53])).
% 0.19/0.48  fof(f153,plain,(
% 0.19/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_15),
% 0.19/0.48    inference(avatar_component_clause,[],[f152])).
% 0.19/0.48  fof(f152,plain,(
% 0.19/0.48    spl6_15 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.48  fof(f194,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_21),
% 0.19/0.48    inference(avatar_component_clause,[],[f193])).
% 0.19/0.48  fof(f193,plain,(
% 0.19/0.48    spl6_21 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.19/0.48  fof(f593,plain,(
% 0.19/0.48    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_27 | ~spl6_37 | ~spl6_40 | ~spl6_44 | ~spl6_48),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f592])).
% 0.19/0.48  fof(f592,plain,(
% 0.19/0.48    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_27 | ~spl6_37 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f191,f548])).
% 0.19/0.48  fof(f548,plain,(
% 0.19/0.48    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_27 | ~spl6_37 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f547,f236])).
% 0.19/0.48  fof(f547,plain,(
% 0.19/0.48    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_37 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f546,f334])).
% 0.19/0.48  fof(f546,plain,(
% 0.19/0.48    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f545,f183])).
% 0.19/0.48  fof(f545,plain,(
% 0.19/0.48    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f544,f161])).
% 0.19/0.48  fof(f544,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f543,f123])).
% 0.19/0.48  fof(f543,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f542,f170])).
% 0.19/0.48  fof(f542,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f541,f91])).
% 0.19/0.48  fof(f91,plain,(
% 0.19/0.48    ~v1_xboole_0(sK0) | spl6_6),
% 0.19/0.48    inference(avatar_component_clause,[],[f90])).
% 0.19/0.48  fof(f90,plain,(
% 0.19/0.48    spl6_6 <=> v1_xboole_0(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.48  fof(f541,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f540,f383])).
% 0.19/0.48  fof(f383,plain,(
% 0.19/0.48    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~spl6_44),
% 0.19/0.48    inference(avatar_component_clause,[],[f382])).
% 0.19/0.48  fof(f382,plain,(
% 0.19/0.48    spl6_44 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.19/0.48  fof(f540,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f539,f367])).
% 0.19/0.48  fof(f367,plain,(
% 0.19/0.48    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_40),
% 0.19/0.48    inference(avatar_component_clause,[],[f366])).
% 0.19/0.48  fof(f366,plain,(
% 0.19/0.48    spl6_40 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.19/0.48  fof(f539,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f538,f153])).
% 0.19/0.48  fof(f538,plain,(
% 0.19/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f537,f106])).
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    v1_funct_2(sK5,sK3,sK1) | ~spl6_9),
% 0.19/0.48    inference(avatar_component_clause,[],[f105])).
% 0.19/0.48  fof(f105,plain,(
% 0.19/0.48    spl6_9 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.19/0.48  fof(f537,plain,(
% 0.19/0.48    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f536,f71])).
% 0.19/0.48  fof(f536,plain,(
% 0.19/0.48    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f535,f157])).
% 0.19/0.48  fof(f535,plain,(
% 0.19/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f534,f112])).
% 0.19/0.48  fof(f112,plain,(
% 0.19/0.48    v1_funct_2(sK4,sK2,sK1) | ~spl6_10),
% 0.19/0.48    inference(avatar_component_clause,[],[f111])).
% 0.19/0.48  fof(f111,plain,(
% 0.19/0.48    spl6_10 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.19/0.48  fof(f534,plain,(
% 0.19/0.48    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f533,f75])).
% 0.19/0.48  fof(f533,plain,(
% 0.19/0.48    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f532,f116])).
% 0.19/0.48  fof(f532,plain,(
% 0.19/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f531,f79])).
% 0.19/0.48  fof(f79,plain,(
% 0.19/0.48    ~v1_xboole_0(sK3) | spl6_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f78])).
% 0.19/0.48  fof(f78,plain,(
% 0.19/0.48    spl6_3 <=> v1_xboole_0(sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.48  fof(f531,plain,(
% 0.19/0.48    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f530,f120])).
% 0.19/0.48  fof(f120,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_12),
% 0.19/0.48    inference(avatar_component_clause,[],[f119])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    spl6_12 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.19/0.48  fof(f530,plain,(
% 0.19/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f529,f83])).
% 0.19/0.48  fof(f83,plain,(
% 0.19/0.48    ~v1_xboole_0(sK2) | spl6_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f82])).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    spl6_4 <=> v1_xboole_0(sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.48  fof(f529,plain,(
% 0.19/0.48    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_5 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f514,f87])).
% 0.19/0.48  fof(f87,plain,(
% 0.19/0.48    ~v1_xboole_0(sK1) | spl6_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f86])).
% 0.19/0.48  fof(f86,plain,(
% 0.19/0.48    spl6_5 <=> v1_xboole_0(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.48  fof(f514,plain,(
% 0.19/0.48    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_48),
% 0.19/0.48    inference(resolution,[],[f399,f68])).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.19/0.48    inference(equality_resolution,[],[f50])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.48    inference(flattening,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,axiom,(
% 0.19/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.19/0.48  fof(f399,plain,(
% 0.19/0.48    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_48),
% 0.19/0.48    inference(avatar_component_clause,[],[f398])).
% 0.19/0.48  fof(f398,plain,(
% 0.19/0.48    spl6_48 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.19/0.48  fof(f191,plain,(
% 0.19/0.48    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_20),
% 0.19/0.48    inference(avatar_component_clause,[],[f190])).
% 0.19/0.48  fof(f190,plain,(
% 0.19/0.48    spl6_20 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.19/0.48  fof(f570,plain,(
% 0.19/0.48    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_19 | ~spl6_27 | ~spl6_37 | ~spl6_40 | ~spl6_44 | ~spl6_48),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f569])).
% 0.19/0.48  fof(f569,plain,(
% 0.19/0.48    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_19 | ~spl6_27 | ~spl6_37 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f568,f236])).
% 0.19/0.48  fof(f568,plain,(
% 0.19/0.48    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_19 | ~spl6_37 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f567,f334])).
% 0.19/0.48  fof(f567,plain,(
% 0.19/0.48    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_19 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f566,f183])).
% 0.19/0.48  fof(f566,plain,(
% 0.19/0.48    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_19 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f565,f161])).
% 0.19/0.48  fof(f565,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | spl6_19 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f564,f123])).
% 0.19/0.48  fof(f564,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | spl6_19 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(forward_demodulation,[],[f563,f170])).
% 0.19/0.48  fof(f563,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | spl6_19 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f562,f188])).
% 0.19/0.48  fof(f188,plain,(
% 0.19/0.48    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_19),
% 0.19/0.48    inference(avatar_component_clause,[],[f187])).
% 0.19/0.48  fof(f187,plain,(
% 0.19/0.48    spl6_19 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.19/0.48  fof(f562,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f561,f91])).
% 0.19/0.48  fof(f561,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_44 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f560,f383])).
% 0.19/0.48  fof(f560,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_40 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f559,f367])).
% 0.19/0.48  fof(f559,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f558,f153])).
% 0.19/0.48  fof(f558,plain,(
% 0.19/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f557,f106])).
% 0.19/0.48  fof(f557,plain,(
% 0.19/0.48    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f556,f71])).
% 0.19/0.48  fof(f556,plain,(
% 0.19/0.48    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f555,f157])).
% 0.19/0.48  fof(f555,plain,(
% 0.19/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f554,f112])).
% 0.19/0.48  fof(f554,plain,(
% 0.19/0.48    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f553,f75])).
% 0.19/0.48  fof(f553,plain,(
% 0.19/0.48    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f552,f116])).
% 0.19/0.48  fof(f552,plain,(
% 0.19/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f551,f79])).
% 0.19/0.48  fof(f551,plain,(
% 0.19/0.48    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_12 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f550,f120])).
% 0.19/0.48  fof(f550,plain,(
% 0.19/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f549,f83])).
% 0.19/0.48  fof(f549,plain,(
% 0.19/0.48    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_5 | ~spl6_48)),
% 0.19/0.48    inference(subsumption_resolution,[],[f515,f87])).
% 0.19/0.48  fof(f515,plain,(
% 0.19/0.48    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_48),
% 0.19/0.48    inference(resolution,[],[f399,f67])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.19/0.48    inference(equality_resolution,[],[f51])).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f400,plain,(
% 0.19/0.48    spl6_48 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16),
% 0.19/0.48    inference(avatar_split_clause,[],[f352,f156,f152,f119,f115,f111,f105,f90,f86,f82,f78,f74,f70,f398])).
% 0.19/0.48  fof(f352,plain,(
% 0.19/0.48    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f351,f79])).
% 0.19/0.48  fof(f351,plain,(
% 0.19/0.48    v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f350,f106])).
% 0.19/0.48  fof(f350,plain,(
% 0.19/0.48    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f349,f71])).
% 0.19/0.48  fof(f349,plain,(
% 0.19/0.48    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f347,f116])).
% 0.19/0.48  fof(f347,plain,(
% 0.19/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(resolution,[],[f258,f153])).
% 0.19/0.48  fof(f258,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f257,f87])).
% 0.19/0.48  fof(f257,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f256,f112])).
% 0.19/0.48  fof(f256,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f255,f75])).
% 0.19/0.48  fof(f255,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (spl6_4 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(resolution,[],[f143,f157])).
% 0.19/0.48  fof(f143,plain,(
% 0.19/0.48    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | v1_xboole_0(X9) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | spl6_6 | ~spl6_12)),
% 0.19/0.48    inference(subsumption_resolution,[],[f142,f91])).
% 0.19/0.48  fof(f142,plain,(
% 0.19/0.48    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | ~spl6_12)),
% 0.19/0.48    inference(subsumption_resolution,[],[f137,f83])).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | ~spl6_12),
% 0.19/0.48    inference(resolution,[],[f120,f49])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.19/0.48    inference(flattening,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.19/0.48  fof(f384,plain,(
% 0.19/0.48    spl6_44 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16),
% 0.19/0.48    inference(avatar_split_clause,[],[f327,f156,f152,f119,f115,f111,f105,f90,f86,f82,f78,f74,f70,f382])).
% 0.19/0.48  fof(f327,plain,(
% 0.19/0.48    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f326,f79])).
% 0.19/0.48  fof(f326,plain,(
% 0.19/0.48    v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f325,f106])).
% 0.19/0.48  fof(f325,plain,(
% 0.19/0.48    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f324,f71])).
% 0.19/0.48  fof(f324,plain,(
% 0.19/0.48    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f322,f116])).
% 0.19/0.48  fof(f322,plain,(
% 0.19/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(resolution,[],[f246,f153])).
% 0.19/0.48  fof(f246,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f245,f87])).
% 0.19/0.48  fof(f245,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f244,f112])).
% 0.19/0.48  % (19727)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.48  fof(f244,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f243,f75])).
% 0.19/0.48  fof(f243,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (spl6_4 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(resolution,[],[f141,f157])).
% 0.19/0.48  fof(f141,plain,(
% 0.19/0.48    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | v1_xboole_0(X5) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | spl6_6 | ~spl6_12)),
% 0.19/0.48    inference(subsumption_resolution,[],[f140,f91])).
% 0.19/0.48  fof(f140,plain,(
% 0.19/0.48    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | ~spl6_12)),
% 0.19/0.48    inference(subsumption_resolution,[],[f136,f83])).
% 0.19/0.48  fof(f136,plain,(
% 0.19/0.48    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | ~spl6_12),
% 0.19/0.48    inference(resolution,[],[f120,f48])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f368,plain,(
% 0.19/0.48    spl6_40 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16),
% 0.19/0.48    inference(avatar_split_clause,[],[f305,f156,f152,f119,f115,f111,f105,f90,f86,f82,f78,f74,f70,f366])).
% 0.19/0.48  fof(f305,plain,(
% 0.19/0.48    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f304,f79])).
% 0.19/0.48  fof(f304,plain,(
% 0.19/0.48    v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f303,f106])).
% 0.19/0.48  fof(f303,plain,(
% 0.19/0.48    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f302,f71])).
% 0.19/0.48  fof(f302,plain,(
% 0.19/0.48    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f300,f116])).
% 0.19/0.48  fof(f300,plain,(
% 0.19/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15 | ~spl6_16)),
% 0.19/0.48    inference(resolution,[],[f233,f153])).
% 0.19/0.48  fof(f233,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f232,f87])).
% 0.19/0.48  fof(f232,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f231,f112])).
% 0.19/0.48  fof(f231,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(subsumption_resolution,[],[f230,f75])).
% 0.19/0.48  fof(f230,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (spl6_4 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.19/0.48    inference(resolution,[],[f139,f157])).
% 0.19/0.48  fof(f139,plain,(
% 0.19/0.48    ( ! [X4,X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | v1_xboole_0(X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | spl6_6 | ~spl6_12)),
% 0.19/0.48    inference(subsumption_resolution,[],[f138,f91])).
% 0.19/0.48  fof(f138,plain,(
% 0.19/0.48    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | ~spl6_12)),
% 0.19/0.48    inference(subsumption_resolution,[],[f135,f83])).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | ~spl6_12),
% 0.19/0.48    inference(resolution,[],[f120,f47])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f335,plain,(
% 0.19/0.48    spl6_37 | ~spl6_22 | ~spl6_26),
% 0.19/0.48    inference(avatar_split_clause,[],[f320,f220,f197,f333])).
% 0.19/0.48  fof(f197,plain,(
% 0.19/0.48    spl6_22 <=> v1_relat_1(sK4)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.19/0.48  fof(f220,plain,(
% 0.19/0.48    spl6_26 <=> sK4 = k7_relat_1(sK4,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.19/0.48  fof(f320,plain,(
% 0.19/0.48    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_22 | ~spl6_26)),
% 0.19/0.48    inference(superposition,[],[f283,f221])).
% 0.19/0.48  fof(f221,plain,(
% 0.19/0.48    sK4 = k7_relat_1(sK4,sK2) | ~spl6_26),
% 0.19/0.48    inference(avatar_component_clause,[],[f220])).
% 0.19/0.48  fof(f283,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)) ) | ~spl6_22),
% 0.19/0.48    inference(resolution,[],[f200,f63])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.48  fof(f200,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),X1)) ) | ~spl6_22),
% 0.19/0.48    inference(resolution,[],[f198,f59])).
% 0.19/0.48  fof(f59,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(flattening,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.19/0.48  fof(f198,plain,(
% 0.19/0.48    v1_relat_1(sK4) | ~spl6_22),
% 0.19/0.48    inference(avatar_component_clause,[],[f197])).
% 0.19/0.48  fof(f237,plain,(
% 0.19/0.48    spl6_27 | ~spl6_18 | ~spl6_25),
% 0.19/0.48    inference(avatar_split_clause,[],[f229,f216,f173,f235])).
% 0.19/0.48  fof(f173,plain,(
% 0.19/0.48    spl6_18 <=> v1_relat_1(sK5)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.19/0.48  fof(f216,plain,(
% 0.19/0.48    spl6_25 <=> sK5 = k7_relat_1(sK5,sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.19/0.48  fof(f229,plain,(
% 0.19/0.48    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_18 | ~spl6_25)),
% 0.19/0.48    inference(superposition,[],[f223,f217])).
% 0.19/0.48  fof(f217,plain,(
% 0.19/0.48    sK5 = k7_relat_1(sK5,sK3) | ~spl6_25),
% 0.19/0.48    inference(avatar_component_clause,[],[f216])).
% 0.19/0.48  fof(f223,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0)) ) | ~spl6_18),
% 0.19/0.48    inference(resolution,[],[f185,f63])).
% 0.19/0.48  fof(f185,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),X1)) ) | ~spl6_18),
% 0.19/0.48    inference(resolution,[],[f174,f59])).
% 0.19/0.48  fof(f174,plain,(
% 0.19/0.48    v1_relat_1(sK5) | ~spl6_18),
% 0.19/0.48    inference(avatar_component_clause,[],[f173])).
% 0.19/0.48  fof(f222,plain,(
% 0.19/0.48    spl6_26 | ~spl6_22 | ~spl6_24),
% 0.19/0.48    inference(avatar_split_clause,[],[f212,f206,f197,f220])).
% 0.19/0.48  fof(f206,plain,(
% 0.19/0.48    spl6_24 <=> v4_relat_1(sK4,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.19/0.48  fof(f212,plain,(
% 0.19/0.48    sK4 = k7_relat_1(sK4,sK2) | (~spl6_22 | ~spl6_24)),
% 0.19/0.48    inference(subsumption_resolution,[],[f211,f198])).
% 0.19/0.48  fof(f211,plain,(
% 0.19/0.48    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK2) | ~spl6_24),
% 0.19/0.48    inference(resolution,[],[f207,f60])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(flattening,[],[f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.19/0.48  fof(f207,plain,(
% 0.19/0.48    v4_relat_1(sK4,sK2) | ~spl6_24),
% 0.19/0.48    inference(avatar_component_clause,[],[f206])).
% 0.19/0.48  fof(f218,plain,(
% 0.19/0.48    spl6_25 | ~spl6_18 | ~spl6_23),
% 0.19/0.48    inference(avatar_split_clause,[],[f210,f202,f173,f216])).
% 0.19/0.48  fof(f202,plain,(
% 0.19/0.48    spl6_23 <=> v4_relat_1(sK5,sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.19/0.48  fof(f210,plain,(
% 0.19/0.48    sK5 = k7_relat_1(sK5,sK3) | (~spl6_18 | ~spl6_23)),
% 0.19/0.48    inference(subsumption_resolution,[],[f209,f174])).
% 0.19/0.48  fof(f209,plain,(
% 0.19/0.48    ~v1_relat_1(sK5) | sK5 = k7_relat_1(sK5,sK3) | ~spl6_23),
% 0.19/0.48    inference(resolution,[],[f203,f60])).
% 0.19/0.48  fof(f203,plain,(
% 0.19/0.48    v4_relat_1(sK5,sK3) | ~spl6_23),
% 0.19/0.48    inference(avatar_component_clause,[],[f202])).
% 0.19/0.48  fof(f208,plain,(
% 0.19/0.48    spl6_24 | ~spl6_16),
% 0.19/0.48    inference(avatar_split_clause,[],[f176,f156,f206])).
% 0.19/0.48  fof(f176,plain,(
% 0.19/0.48    v4_relat_1(sK4,sK2) | ~spl6_16),
% 0.19/0.48    inference(resolution,[],[f157,f64])).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.48  fof(f204,plain,(
% 0.19/0.48    spl6_23 | ~spl6_15),
% 0.19/0.48    inference(avatar_split_clause,[],[f163,f152,f202])).
% 0.19/0.48  fof(f163,plain,(
% 0.19/0.48    v4_relat_1(sK5,sK3) | ~spl6_15),
% 0.19/0.48    inference(resolution,[],[f153,f64])).
% 0.19/0.48  fof(f199,plain,(
% 0.19/0.48    spl6_22 | ~spl6_16),
% 0.19/0.48    inference(avatar_split_clause,[],[f184,f156,f197])).
% 0.19/0.48  fof(f184,plain,(
% 0.19/0.48    v1_relat_1(sK4) | ~spl6_16),
% 0.19/0.48    inference(subsumption_resolution,[],[f178,f55])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.48  fof(f178,plain,(
% 0.19/0.48    ~v1_relat_1(k2_zfmisc_1(sK2,sK1)) | v1_relat_1(sK4) | ~spl6_16),
% 0.19/0.48    inference(resolution,[],[f157,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.48  fof(f195,plain,(
% 0.19/0.48    ~spl6_19 | ~spl6_20 | ~spl6_21),
% 0.19/0.48    inference(avatar_split_clause,[],[f33,f193,f190,f187])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.48    inference(flattening,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,negated_conjecture,(
% 0.19/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.19/0.48    inference(negated_conjecture,[],[f13])).
% 0.19/0.48  fof(f13,conjecture,(
% 0.19/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.19/0.48  fof(f175,plain,(
% 0.19/0.48    spl6_18 | ~spl6_15),
% 0.19/0.48    inference(avatar_split_clause,[],[f171,f152,f173])).
% 0.19/0.48  fof(f171,plain,(
% 0.19/0.48    v1_relat_1(sK5) | ~spl6_15),
% 0.19/0.48    inference(subsumption_resolution,[],[f165,f55])).
% 0.19/0.48  fof(f165,plain,(
% 0.19/0.48    ~v1_relat_1(k2_zfmisc_1(sK3,sK1)) | v1_relat_1(sK5) | ~spl6_15),
% 0.19/0.48    inference(resolution,[],[f153,f58])).
% 0.19/0.48  fof(f162,plain,(
% 0.19/0.48    spl6_17 | ~spl6_8),
% 0.19/0.48    inference(avatar_split_clause,[],[f108,f101,f160])).
% 0.19/0.48  fof(f101,plain,(
% 0.19/0.48    spl6_8 <=> r1_xboole_0(sK2,sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.19/0.48  fof(f108,plain,(
% 0.19/0.48    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_8),
% 0.19/0.48    inference(resolution,[],[f102,f62])).
% 0.19/0.48  fof(f62,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    r1_xboole_0(sK2,sK3) | ~spl6_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f101])).
% 0.19/0.48  fof(f158,plain,(
% 0.19/0.48    spl6_16),
% 0.19/0.48    inference(avatar_split_clause,[],[f39,f156])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f154,plain,(
% 0.19/0.48    spl6_15),
% 0.19/0.48    inference(avatar_split_clause,[],[f36,f152])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f121,plain,(
% 0.19/0.48    spl6_12),
% 0.19/0.48    inference(avatar_split_clause,[],[f44,f119])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f117,plain,(
% 0.19/0.48    spl6_11),
% 0.19/0.48    inference(avatar_split_clause,[],[f41,f115])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f113,plain,(
% 0.19/0.48    spl6_10),
% 0.19/0.48    inference(avatar_split_clause,[],[f38,f111])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    v1_funct_2(sK4,sK2,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f107,plain,(
% 0.19/0.48    spl6_9),
% 0.19/0.48    inference(avatar_split_clause,[],[f35,f105])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    v1_funct_2(sK5,sK3,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f103,plain,(
% 0.19/0.48    spl6_8 | spl6_3 | spl6_4 | ~spl6_7),
% 0.19/0.48    inference(avatar_split_clause,[],[f99,f94,f82,f78,f101])).
% 0.19/0.48  fof(f94,plain,(
% 0.19/0.48    spl6_7 <=> r1_subset_1(sK2,sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    r1_xboole_0(sK2,sK3) | (spl6_3 | spl6_4 | ~spl6_7)),
% 0.19/0.48    inference(subsumption_resolution,[],[f98,f83])).
% 0.19/0.48  fof(f98,plain,(
% 0.19/0.48    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | (spl6_3 | ~spl6_7)),
% 0.19/0.48    inference(subsumption_resolution,[],[f97,f79])).
% 0.19/0.48  fof(f97,plain,(
% 0.19/0.48    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_7),
% 0.19/0.48    inference(resolution,[],[f95,f57])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.19/0.49    inference(flattening,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.19/0.49  fof(f95,plain,(
% 0.19/0.49    r1_subset_1(sK2,sK3) | ~spl6_7),
% 0.19/0.49    inference(avatar_component_clause,[],[f94])).
% 0.19/0.49  fof(f96,plain,(
% 0.19/0.49    spl6_7),
% 0.19/0.49    inference(avatar_split_clause,[],[f42,f94])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    r1_subset_1(sK2,sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    ~spl6_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f46,f90])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ~v1_xboole_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    ~spl6_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f45,f86])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ~v1_xboole_0(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    ~spl6_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f43,f82])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ~v1_xboole_0(sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    ~spl6_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f40,f78])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ~v1_xboole_0(sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    spl6_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f37,f74])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    v1_funct_1(sK4)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    spl6_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f34,f70])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    v1_funct_1(sK5)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (19725)------------------------------
% 0.19/0.49  % (19725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19725)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (19725)Memory used [KB]: 6780
% 0.19/0.49  % (19725)Time elapsed: 0.080 s
% 0.19/0.49  % (19725)------------------------------
% 0.19/0.49  % (19725)------------------------------
% 0.19/0.49  % (19724)Success in time 0.141 s
%------------------------------------------------------------------------------
